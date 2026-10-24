"""Regression test for the input hardening of `nmms-lean` (Main.lean).

Stdlib only; runs the built binary with a list argv (no shell). Checks:
  * 27 malformed or over-limit inputs each return an {"error": ...} line within
    5 seconds: a line over the byte cap, nesting over the depth cap (1,000,000
    nested `neg`), a base without "consequences", a wrong-typed field
    ("unless": 5), an unknown "engine", a certificate with the wrong number of
    premises for its rule; an unpaired UTF-16 surrogate escape, which
    `Json.parse` would read as U+FFFD (a lone low one, also in upper-case hex
    and after an escaped backslash; a lone high one; a high one followed by a
    non-surrogate escape); robustness that pyNMMS refuses (defeaters on a
    MONOTONE entry or on one with no "kind", "unless": 5 on a MONOTONE entry,
    an empty exclusion pair); a formula object with two keys, a non-string
    atom; a certificate with side "X", an {"ax": false} leaf, a node with both
    "ax" and "side", a node with an unknown key, a "keep" of null, a rule
    node on an atom; a repeated key, which `Json.parse` would read by its last
    value (in a formula, in a certificate leaf, spelled with an escape); a
    defeater atom outside the base's language;
  * 3 well-formed queries (same shape as the difftest corpus) return exactly
    the expected answers (captured from the pre-hardening build; the third
    changed when Containment stopped being added: over the empty base
    `p, q ⇒ q` is not an axiom, so `p ∧ q ⇒ q` is not derivable and its
    certificate is rejected);
  * 7 well-formed queries that the checks above must not refuse return
    exactly the expected answers: an atom written as a surrogate-pair escape
    (an emoji, which `json.dumps` sends as a high and a low escape; a
    different emoji stays a different atom), an escaped backslash followed
    by `udc80` (not an escape), robustness that pyNMMS accepts
    ({"kind": "monotone", "unless": {}} and the plain string "monotone"), and
    atoms containing ":" (also after an escaped quote), which the
    repeated-key check counts only outside strings.

Run (from anywhere, after `lake build`):  python3 -I difftest/malformed_test.py
Exit status 0 only if all 37 checks pass.
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


def atom_query(base_atom, query_atom):
    """`base_atom |~ q` (no language), asking `query_atom => q`."""
    return query(base={"consequences": [{"antecedent": [base_atom], "consequent": ["q"]}]},
                 antecedent=[{"atom": query_atom}])


def rob_query(rob, antecedent=(P,)):
    """`p |~ q` with this robustness, asking `antecedent => q`."""
    return query(base={"language": ["p", "q", "r", "s"], "consequences": [
        {"antecedent": ["p"], "consequent": ["q"], "robustness": rob}]},
        antecedent=list(antecedent))


BACKSLASH = "\\"
UNPAIRED = "unpaired UTF-16 surrogate escape"

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
    # json.dumps (ensure_ascii, the default) writes each lone surrogate as an escape.
    "lone low surrogate escape": (atom_query("<\udc80>", "<\udc81>"), [], UNPAIRED),
    "lone low surrogate escape in upper-case hex": (
        atom_query("q", "<\udc81>").replace(BACKSLASH + "udc81", BACKSLASH + "uDC81"), [], UNPAIRED),
    "lone low surrogate escape after an escaped backslash": (
        atom_query("q", BACKSLASH + "\udc80"), [], UNPAIRED),
    "lone high surrogate escape": (atom_query("<\ud800>", "<\ud801>"), [], UNPAIRED),
    "high surrogate escape followed by a non-surrogate escape": (
        atom_query("\ud800\xe9", "\ud800\xe8"), [], UNPAIRED),
    "defeaters on a MONOTONE entry": (
        rob_query({"kind": "monotone", "unless": {"antecedent": ["r"]}}, [P, {"atom": "r"}]), [],
        "not monotone"),
    'defeaters on an entry with no "kind" (EXACT)': (
        rob_query({"unless": {"antecedent": ["r"]}}), [], "not exact"),
    'MONOTONE entry with "unless": 5': (
        rob_query({"kind": "monotone", "unless": 5}), [], "unless must be an object"),
    "GUARDED entry with an empty exclusion pair": (
        rob_query({"kind": "guarded", "unless": {"pairs": [{"antecedent": [], "consequent": []}]}}),
        [], "at least one atom"),
    "formula object with two keys": (
        query(antecedent=[{"atom": "p", "neg": Q}]), [], "not a formula"),
    "formula atom that is not a string": (
        query(antecedent=[{"atom": 5}]), [], "atom must be a string"),
    'certificate side "X"': (
        query(antecedent=[CONJ], cert={"side": "X", "principal": CONJ, "premises": [{"ax": True}] * 3}),
        [], 'side must be "L" or "R"'),
    'certificate leaf {"ax": false}': (
        query(antecedent=[CONJ], cert={"side": "L", "principal": CONJ, "premises": [{"ax": False}]}),
        [], '"ax" must be true'),
    'certificate node with both "ax" and "side"': (
        query(antecedent=[CONJ], cert={"ax": True, "side": "L", "principal": CONJ,
                                       "premises": [{"ax": True}]}), [], "not both"),
    "certificate node with an unknown key": (
        query(antecedent=[CONJ], cert={"side": "L", "principal": CONJ, "premises": [{"ax": True}],
                                       "note": "x"}), [], "unknown key note"),
    'certificate "keep": null': (
        query(antecedent=[CONJ], cert={"side": "L", "principal": CONJ, "keep": None,
                                       "premises": [{"ax": True}]}), [], "keep must be a boolean"),
    "certificate rule node on an atom": (
        query(cert={"side": "L", "principal": P, "premises": []}), [], "an atom has no rule"),
    # json.dumps cannot repeat a key, so these lines are written out.
    "repeated key in a formula": (
        '{"id":1,"base":{"language":["p","q","r"],"consequences":[{"antecedent":["p"],'
        '"consequent":["q"]}]},"antecedent":[{"atom":"r","atom":"p"}],"consequent":[{"atom":"q"}]}\n',
        [], "repeats a key"),
    "repeated key in a certificate leaf": (
        '{"id":1,"base":{"language":["p","q"],"consequences":[{"antecedent":["p"],'
        '"consequent":["q"]}]},"antecedent":[{"atom":"p"}],"consequent":[{"atom":"q"}],'
        '"cert":{"ax":false,"ax":true}}\n', [], "repeats a key"),
    "repeated key spelled with an escape": (
        '{"id":1,"base":{"language":["p","q","r"],"consequences":[{"antecedent":["p"],'
        '"consequent":["q"]}]},"antecedent":[{"atom":"r","\\u0061tom":"p"}],'
        '"consequent":[{"atom":"q"}]}\n', [], "repeats a key"),
    "defeater atom outside the language": (
        rob_query({"kind": "guarded", "unless": {"antecedent": ["zzz"]}}), [],
        "atom zzz in the base is not in the base's language"),
}

# Expected answers on these three corpus-shaped queries (see the header).
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
     {"cert_ok": False, "derivable": False, "id": 1, "refute_len": 1, "refute_ok": True}),
]

# Well-formed inputs next to the refusals above, which must still be answered.
DERIVABLE = {"cert_ok": None, "derivable": True, "id": 1, "refute_len": None, "refute_ok": None}
UNDERIVABLE = {"cert_ok": None, "derivable": False, "id": 1, "refute_len": 0, "refute_ok": True}
accepted_cases = {
    "surrogate-pair escape: the same emoji": (
        atom_query("\U0001F600", "\U0001F600"), DERIVABLE),
    "surrogate-pair escape: another emoji is another atom": (
        atom_query("\U0001F600", "\U0001F601"), UNDERIVABLE),
    "escaped backslash then udc80 (not an escape)": (
        atom_query(BACKSLASH + "udc80", BACKSLASH + "udc80"), DERIVABLE),
    '{"kind": "monotone", "unless": {}} (pyNMMS accepts it)': (
        rob_query({"kind": "monotone", "unless": {}}, [P, {"atom": "r"}]), DERIVABLE),
    'robustness "monotone" as a plain string (pyNMMS accepts it)': (
        rob_query("monotone", [P, {"atom": "r"}]), DERIVABLE),
    'an atom containing ":"': (atom_query("a:b", "a:b"), DERIVABLE),
    'an atom containing an escaped quote and ":"': (atom_query('a":b', 'a":b'), DERIVABLE),
}

passed = failed = 0
for name, (text, args, *reason) in error_cases.items():
    try:
        out = run(text, args)
        good = len(out) == 1 and "error" in out[0] and all(r in out[0]["error"] for r in reason)
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
for name, (text, want) in accepted_cases.items():
    try:
        out = run(text)
        good = out == [want]
    except subprocess.TimeoutExpired:
        out, good = "timeout", False
    print(("PASS" if good else "FAIL"), "accepted:", name, "" if good else out)
    passed, failed = (passed + 1, failed) if good else (passed, failed + 1)
print(f"{passed} of {passed + failed} passed")
sys.exit(1 if failed else 0)
