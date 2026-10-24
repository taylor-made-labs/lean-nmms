"""Regression tests: nmms-lean answers NMMS derivability from the supplied base.

Stdlib only (no pyNMMS). Runs the built executable on JSON queries and
checks it against the chapter's rules (Hlobil and Brandom 2025, ch. 3,
pp. 108-111) as implemented independently in difftest/nmms_reference.py:

  * no Containment is added: over the empty base `p => p` is not derivable;
  * an atomic sequent is derivable exactly when it is in the base;
  * with Containment supplied in the base, classical tautologies return;
  * the default engine agrees with the reference on random bases and
    sequents (the backtracking engine too, on sequents with at most
    BACKTRACK_MAX connectives: it is exponential in the worst case), every
    "not derivable" carries an accepted refutation, and a full-decomposition
    certificate (some steps using the book's instance whose context keeps the
    principal sentence) is accepted exactly when the sequent is derivable
    (certificates over CERT_MAX_BYTES are not sent);
  * a query outside the base's language, or a base listing a pair twice, is
    refused; the closure operation reports "in_closure", never "derivable".

Run (after `lake build`):  python3 -B -m unittest -v tests.test_nmms_rules
"""

import hashlib
import itertools
import json
import os
import random
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "difftest"))
import nmms_reference as ref  # noqa: E402

EXE = Path(os.environ.get("NMMS_LEAN_EXE", ROOT / ".lake/build/bin/nmms-lean"))
CASES = int(os.environ.get("NMMS_RULES_CASES", "1500"))
BACKTRACK_MAX = 7
CERT_MAX_BYTES = 1_000_000  # larger certificates are skipped (the line cap is 4 MiB)

P, Q, R = {"atom": "p"}, {"atom": "q"}, {"atom": "r"}


def neg(a):
    return {"neg": a}


def conj(a, b):
    return {"conj": [a, b]}


def disj(a, b):
    return {"disj": [a, b]}


def impl(a, b):
    return {"impl": [a, b]}


def base(*entries, language=("p", "q", "r")):
    cons = []
    for e in entries:
        ant, con, *kind = e
        cons.append({"antecedent": list(ant), "consequent": list(con),
                     "robustness": {"kind": kind[0] if kind else "exact"}})
    return {"language": list(language), "consequences": cons}


def run(queries, timeout=600):
    """Send queries (dicts) in one process; return the answers in order."""
    assert EXE.is_file(), f"run `lake build` first: {EXE}"
    text = "".join(json.dumps(q) + "\n" for q in queries)
    out = subprocess.run([str(EXE)], input=text, capture_output=True, text=True, timeout=timeout)
    assert out.returncode == 0, out.stderr
    answers = [json.loads(line) for line in out.stdout.splitlines()]
    assert len(answers) == len(queries), out.stdout
    return answers


def connectives(f):
    if "atom" in f:
        return 0
    if "neg" in f:
        return 1 + connectives(f["neg"])
    (a, b), = f.values()
    return 1 + connectives(a) + connectives(b)


def ask(b, ant, con, **extra):
    return {"base": b, "antecedent": ant, "consequent": con, **extra}


class NoContainmentAdded(unittest.TestCase):
    def test_empty_base_derives_nothing(self):
        empty = base()
        cases = [([P], [P]), ([neg(P)], [neg(P)]), ([], [disj(P, neg(P))]), ([conj(P, Q)], [P]),
                 ([], [impl(P, P)]), ([P, Q], [P, Q]), ([], []), ([P], [disj(P, Q)])]
        qs = []
        for i, (a, c) in enumerate(cases):
            qs.append(ask(empty, a, c, id=f"fast{i}"))
            qs.append(ask(empty, a, c, id=f"bt{i}", engine="backtracking"))
        for out in run(qs):
            with self.subTest(case=out["id"]):
                self.assertIs(out["derivable"], False, out)
                self.assertIs(out["refute_ok"], True, out)

    def test_shared_atom_needs_the_base(self):
        b = base((["p"], ["q"]))
        outs = run([ask(b, [P], [P], id=1), ask(b, [P], [Q], id=2), ask(b, [P, Q], [Q], id=3)])
        self.assertEqual([o["derivable"] for o in outs], [False, True, False])

    def test_axiom_leaf_must_be_in_the_base(self):
        # p & q => q by L&: the leaf p, q => q is an axiom only if the base has it
        cert = {"side": "L", "principal": conj(P, Q), "premises": [{"ax": True}]}
        outs = run([ask(base(), [conj(P, Q)], [Q], id=1, cert=cert),
                    ask(base((["p", "q"], ["q"])), [conj(P, Q)], [Q], id=2, cert=cert),
                    ask(base(), [P], [P], id=3, cert={"ax": True})])
        self.assertEqual([(o["derivable"], o["cert_ok"]) for o in outs],
                         [(False, False), (True, True), (False, False)])


class BaseExactlyPreserved(unittest.TestCase):
    def test_atomic_sequents_are_exactly_the_base(self):
        rng = random.Random(7)
        names = ["p", "q", "r"]
        subsets = [list(s) for k in range(4) for s in itertools.combinations(names, k)]
        qs, want = [], []
        for _ in range(12):
            b = ref.gen_base(rng, names, max_entries=6)
            rel = ref.Base(b)
            for X in subsets:
                for Y in subsets:
                    qs.append(ask(b, [{"atom": a} for a in X], [{"atom": a} for a in Y],
                                  id=len(qs)))
                    want.append(rel.contains(frozenset(X), frozenset(Y)))
        outs = run(qs)
        self.assertEqual([o["derivable"] for o in outs], want)


class ContainmentSupplied(unittest.TestCase):
    def test_classical_tautologies_with_containment_in_the_base(self):
        b = ref.with_containment(base())
        taut = [([P], [P]), ([], [disj(P, neg(P))]), ([conj(P, Q)], [P]), ([], [impl(P, P)]),
                ([impl(P, Q), P], [Q]), ([neg(neg(P))], [P]), ([disj(P, Q)], [Q, P])]
        non = [([disj(P, Q)], [P]), ([P], [Q]), ([], [P])]
        outs = run([ask(b, a, c, id=i) for i, (a, c) in enumerate(taut + non)])
        self.assertEqual([o["derivable"] for o in outs], [True] * len(taut) + [False] * len(non))


class AgainstReference(unittest.TestCase):
    def test_random_cases(self):
        rng = random.Random(20261024)
        names = ["p", "q", "r", "s"]
        qs, meta = [], []
        while len(meta) < CASES:
            b = rng.choice([ref.gen_base(rng, names), ref.with_containment(ref.gen_base(rng, names))])
            rel = ref.Base(b)
            prover = ref.make_prover(rel)
            for _ in range(3):
                ant = [ref.gen_formula(rng, names, rng.randint(0, 3)) for _ in range(rng.randint(0, 3))]
                con = [ref.gen_formula(rng, names, rng.randint(0, 3)) for _ in range(rng.randint(0, 3))]
                G = frozenset(ref.freeze(f) for f in ant)
                D = frozenset(ref.freeze(f) for f in con)
                want = prover(G, D)
                cert = ref.decomposition_cert(G, D, rng, keeps=2)
                if len(json.dumps(cert)) > CERT_MAX_BYTES:
                    cert = None
                # Lean gets shuffled sides with duplicates.
                lant = ant + [f for f in ant if rng.random() < 0.3]
                lcon = con + [f for f in con if rng.random() < 0.3]
                rng.shuffle(lant)
                rng.shuffle(lcon)
                i = len(meta)
                small = sum(map(connectives, ant + con)) <= BACKTRACK_MAX
                qs.append(ask(b, lant, lcon, id=f"{i}f", **({"cert": cert} if cert else {})))
                if small:
                    qs.append(ask(b, lant, lcon, id=f"{i}b", engine="backtracking"))
                meta.append((want, b, ant, con, small, cert is not None))
        outs = {o["id"]: o for o in run(qs)}
        bad = []
        for k, (want, b, ant, con, small, has_cert) in enumerate(meta):
            fast, back = outs[f"{k}f"], outs.get(f"{k}b", {"derivable": want})
            ok = (fast.get("derivable") is want and back.get("derivable") is want
                  and fast.get("cert_ok") is (want if has_cert else None)
                  and (want or fast.get("refute_ok") is True))
            if not ok:
                bad.append({"want": want, "fast": fast, "back": back, "base": b,
                            "ant": ant, "con": con})
        self.assertEqual(bad[:3], [], f"{len(bad)} of {len(meta)} cases differ")
        self.assertGreater(sum(1 for m in meta if m[4]), len(meta) // 3)
        self.assertGreater(sum(1 for m in meta if m[5]), len(meta) - len(meta) // 50)
        derivable = sum(1 for m in meta if m[0])
        self.assertGreater(derivable, len(meta) // 10)
        self.assertLess(derivable, len(meta) - len(meta) // 10)


class InputChecks(unittest.TestCase):
    def test_language_and_duplicate_pairs(self):
        outs = run([
            ask(base(language=("p",)), [R], [P], id="atom-outside"),
            {"id": "base-outside", "base": {"language": ["p"], "consequences": [
                {"antecedent": ["p"], "consequent": ["q"]}]}, "antecedent": [], "consequent": []},
            {"id": "dup", "base": {"language": ["p", "q"], "consequences": [
                {"antecedent": ["p"], "consequent": ["q"]},
                {"antecedent": ["p"], "consequent": ["q"], "robustness": {"kind": "monotone"}}]},
             "antecedent": [P], "consequent": [Q]},
            ask(base(language=("p",)), [P], [P], id="cert-outside",
                cert={"side": "L", "principal": neg(Q), "premises": [{"ax": True}]}),
            ask(base(), [P], [P], id="bad-keep",
                cert={"side": "L", "principal": neg(Q), "keep": 1, "premises": [{"ax": True}]}),
            {"id": "no-language", "base": {"consequences": [
                {"antecedent": ["x"], "consequent": ["y"]}]},
             "antecedent": [{"atom": "x"}], "consequent": [{"atom": "y"}]},
        ])
        for out in outs[:5]:
            with self.subTest(case=out["id"]):
                self.assertIn("error", out)
        self.assertIs(outs[5].get("derivable"), True, outs[5])

    def test_closure_is_not_reported_as_derivability(self):
        a, b, c = {"atom": "a"}, {"atom": "b"}, {"atom": "c"}
        req = {"op": "closure", "id": "chain", "base": {"language": ["a", "b", "c"], "consequences": [
            {"antecedent": ["a"], "consequent": ["b"]}, {"antecedent": ["b"], "consequent": ["c"]}]},
            "initial_premises": [a], "claim": c}
        canon = json.dumps({k: req[k] for k in ("op", "base", "initial_premises", "claim")},
                           sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        req["request_hash"] = hashlib.sha256(canon.encode()).hexdigest()
        req["certificate"] = {"kind": "derivation", "steps": [
            {"premises": [a], "conclusion": b, "cert": {"ax": True}},
            {"premises": [b], "conclusion": c, "cert": {"ax": True}}]}
        seq = ask(req["base"], [a], [c], id="sequent")
        closure, sequent = run([req, seq])
        self.assertIs(closure["accepted"], True, closure)
        self.assertIs(closure["in_closure"], True, closure)
        self.assertNotIn("derivable", closure)
        # c is reachable by chaining, but a => c is not an NMMS sequent (no Cut).
        self.assertIs(sequent["derivable"], False, sequent)


if __name__ == "__main__":
    unittest.main(verbosity=2)
