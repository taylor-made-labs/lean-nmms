"""Lean acceptance: compile kernel examples, audit sources and all dependencies."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import unittest

LEAN = Path(__file__).resolve().parents[1]
EXE = Path(os.environ.get("NMMS_LEAN_EXE", LEAN / ".lake/build/bin/nmms-lean"))


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False).encode("utf-8")


def request_hash(request):
    keys = ("op", "base", "initial_premises", "claim")
    return hashlib.sha256(canonical({k: request[k] for k in keys})).hexdigest()


def ask(request, *, timeout=30):
    """Send one closure request to the built executable and check the reply."""
    assert EXE.is_file(), f"run `lake build` first: {EXE}"
    request = {**request, "request_hash": request_hash(request)}
    result = subprocess.run([str(EXE)], input=canonical(request).decode() + "\n",
                            text=True, capture_output=True, timeout=timeout)
    assert result.returncode == 0, result.stderr
    lines = result.stdout.splitlines()
    assert len(lines) == 1, result.stdout
    out = json.loads(lines[0])
    assert out.get("id") == request["id"], out
    assert out.get("request_hash") == request["request_hash"], out
    assert isinstance(out.get("accepted"), bool), out
    return out


def code_only(text):
    """Remove nested Lean comments and strings without hiding following tokens."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.append(" ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.append(" ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                break
            out.append("\n")
            i = end + 1
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


class LeanAcceptance(unittest.TestCase):
    def lean(self, file):
        proc = subprocess.run(["lake", "env", "lean", file], cwd=LEAN,
                              text=True, capture_output=True, timeout=120)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        return proc.stdout

    def test_ordered_derivation_kernel_examples(self):
        self.lean("tests/FixesDerivation.lean")

    def test_ground_and_entitlement_kernel_examples(self):
        self.lean("tests/FixesGround.lean")

    def test_nmms_rule_kernel_examples(self):
        self.lean("tests/NmmsRules.lean")

    def test_book_rule_correspondence(self):
        self.assertIn("BOOK_RULES_AXIOMS_OK", self.lean("tests/BookRules.lean"))

    def test_compiled_project_proofs(self):
        proc = subprocess.run(
            ["lake", "env", "leanchecker", "--verbose", "LeanNmms", "Main"],
            cwd=LEAN, text=True, capture_output=True, timeout=120,
        )
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        output = proc.stdout + proc.stderr
        self.assertIn("replaying Main", output)
        self.assertIn("replaying LeanNmms.Calculus", output)

    def test_ordered_derivation_json_entry_point(self):
        a, b, c, z = [{"atom": name} for name in ("seed", "mid", "ready", "intruder")]
        base = {"language": ["seed", "mid", "ready", "intruder"], "consequences": [
            {"antecedent": ["seed"], "consequent": ["mid"], "robustness": {"kind": "exact"}},
            {"antecedent": ["mid"], "consequent": ["ready"], "robustness": {"kind": "exact"}},
            {"antecedent": ["intruder"], "consequent": ["ready"], "robustness": {"kind": "exact"}}]}
        first = {"premises": [a], "conclusion": b, "cert": {"ax": True}}
        second = {"premises": [b], "conclusion": c, "cert": {"ax": True}}
        injected = {"premises": [z], "conclusion": c, "cert": {"ax": True}}
        for name, steps, wanted in (
            ("ordered", [first, second], True),
            ("injected", [injected], False),
            ("out-of-order", [second, first], False),
            ("truncated", [first], False),
            ("forged-local-proof", [{"premises": [a], "conclusion": c, "cert": {"ax": True}}], False),
        ):
            with self.subTest(case=name):
                result = ask({"op": "closure", "id": name, "base": base,
                              "initial_premises": [a], "claim": c,
                              "certificate": {"kind": "derivation", "steps": steps}})
                self.assertIs(result["accepted"], wanted, result)
                # closure membership is reported as such, never as derivability
                self.assertNotIn("derivable", result)
                self.assertIs(result["in_closure"], True if wanted else None, result)
                if not wanted:
                    self.assertTrue(result.get("reason"), result)

    def test_no_forbidden_proof_or_foreign_code(self):
        files = [p for p in LEAN.rglob("*.lean")
                 if not any(part.startswith(".") for part in p.relative_to(LEAN).parts)]
        self.assertTrue(files)
        bad = []
        for file in files:
            for token in re.finditer(r"\b(?:sorry|admit|native_decide|extern|axiom)\b",
                                     code_only(file.read_text())):
                bad.append(f"{file.relative_to(LEAN)}: {token.group()}")
        self.assertEqual(bad, [])

    def test_existing_axioms_output_and_all_project_constants(self):
        output = self.lean("Axioms.lean")
        # #print axioms must actually run and produce no unexpected dependency.
        self.assertIn("NMMS.check_sound", output)
        for bracket in re.findall(r"\[([^\]]*)\]", output, re.S):
            self.assertLessEqual(set(re.findall(r"[A-Za-z_][\w.]*", bracket)),
                                 {"propext", "Classical.choice", "Quot.sound"})
        self.assertIn("FIXES_AXIOMS_OK", self.lean("tests/AllConstantsAxioms.lean"))


def load_tests(loader, suite, pattern):
    # CI explicitly names this module. Include the independent forward-rule
    # suite there too; unittest discovery finds its own module separately.
    if pattern is None:
        from tests import test_nmms_forward
        suite.addTests(loader.loadTestsFromModule(test_nmms_forward))
    return suite


if __name__ == "__main__":
    unittest.main(verbosity=2)
