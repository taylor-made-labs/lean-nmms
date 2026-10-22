"""Regression test for the input hardening of `nmms-lean` (Main.lean).

Stdlib only; runs the built binary with a list argv (no shell). Checks:
  * 6 malformed or over-limit inputs each return an {"error": ...} line within
    5 seconds: a line over the byte cap, nesting over the depth cap (1,000,000
    nested `neg`), a base without "consequences", a wrong-typed field
    ("unless": 5), an unknown "engine", a certificate with the wrong number of
    premises for its rule;
  * 3 well-formed queries (same shape as the difftest corpus) still return
    exactly the answers the binary gave before the hardening (captured from
    the pre-change build).

Run (from anywhere, after `lake build`):  python3 -I difftest/malformed_test.py
Exit status 0 only if all 9 checks pass.
"""

import json
import subprocess
import sys
from pathlib import Path

EXE = Path(__file__).resolve().parent.parent / ".lake" / "build" / "bin" / "nmms-lean"
TIMEOUT_S = 5

BASE = {"language": ["p", "q"], "consequences": []}
P, Q = {"atom": "p"}, {"atom": "q"}
CONJ = {"conj": [P, Q]}


def run(stdin_text, args=()):
    r = subprocess.run([str(EXE), *args], input=stdin_text, capture_output=True,
                       text=True, timeout=TIMEOUT_S)
    return [json.loads(l) for l in r.stdout.splitlines() if l.strip()]


def query(**kw):
    q = {"id": 1, "base": BASE, "antecedent": [P], "consequent": [Q]}
    q.update(kw)
    return json.dumps(q) + "\n"


N = 1_000_000
deep = "{\"neg\":" * N + "{\"atom\":\"p\"}" + "}" * N
BIG = "100000000"  # lift the byte cap so the depth cap is what is tested

error_cases = {
    "line over the byte cap": (
        query(id="x" * 3000), ["--max-line-bytes", "1000"]),
    "depth over the cap (1,000,000 nested neg)": (
        json.dumps({"id": 1, "base": BASE, "antecedent": [], "consequent": []})
        [:-1] + ',"antecedent":[' + deep + "]}\n", ["--max-line-bytes", BIG]),
    "base without consequences": (
        query(base={"language": ["p"]}), []),
    'wrong-typed field ("unless": 5)': (
        query(base={"language": ["p", "q"], "consequences": [
            {"antecedent": ["p"], "consequent": ["q"],
             "robustness": {"kind": "guarded", "unless": 5}}]}), []),
    "unknown engine": (query(engine="bogus"), []),
    "certificate with wrong premises count": (
        query(antecedent=[CONJ], cert={"side": "L", "principal": CONJ, "premises": []}),
        []),
}

# Answers of the pre-hardening binary on these three corpus-shaped queries.
ok_cases = [
    (query(base={"language": ["p", "q", "r", "s"], "consequences": [
        {"antecedent": ["p"], "consequent": ["q"], "robustness": {"kind": "exact"}}]}),
     {"cert_ok": None, "derivable": True, "id": 1, "refute_len": None, "refute_ok": None}),
    (query(base={"language": ["p", "q", "r", "s"], "consequences": [
        {"antecedent": ["p"], "consequent": ["q"], "robustness": {
            "kind": "guarded", "unless": {"antecedent": ["r"], "consequent": [],
                                           "pairs": [{"antecedent": ["s"], "consequent": ["q"]}]}}}]},
           antecedent=[P, {"atom": "r"}]),
     {"cert_ok": None, "derivable": False, "id": 1, "refute_len": 0, "refute_ok": True}),
    (query(antecedent=[CONJ], cert={"side": "L", "principal": CONJ, "premises": [{"ax": True}]}),
     {"cert_ok": True, "derivable": True, "id": 1, "refute_len": None, "refute_ok": None}),
]

passed = failed = 0
for name, (text, args) in error_cases.items():
    try:
        out = run(text, args)
        good = len(out) == 1 and "error" in out[0]
    except subprocess.TimeoutExpired:
        out, good = "timeout", False
    print(("PASS" if good else "FAIL"), "error:", name, "" if good else out)
    passed, failed = (passed + 1, failed) if good else (passed, failed + 1)
for i, (text, want) in enumerate(ok_cases, 1):
    try:
        out = run(text)
        good = out == [want]
    except subprocess.TimeoutExpired:
        out, good = "timeout", False
    print(("PASS" if good else "FAIL"), f"unchanged answer {i}", "" if good else out)
    passed, failed = (passed + 1, failed) if good else (passed, failed + 1)
print(f"{passed} of {passed + failed} passed")
sys.exit(1 if failed else 0)
