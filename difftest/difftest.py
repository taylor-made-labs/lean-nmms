"""Differential test: pyNMMS 0.15.1 against the Lean NMMS decision procedure.

Purpose. The Lean procedures (`NMMS.fastProve`, `NMMS.prove`) are proved
to accept exactly the sequents NMMS derives from the supplied base. pyNMMS
differs from NMMS in one known way: its axiom test also accepts every
sequent whose sides share an atom or a complex sentence, i.e. it adds
Containment to the base. So this harness checks two things on generated
bases and sequents:

* pyNMMS over a base B agrees with Lean over B plus explicit Containment
  (a MONOTONE `a |~ a` entry for each atom of the language), so that the
  Lean proofs say something about the running Python reasoner (the Cedar
  method: a proved model plus differential random testing of the production
  code). pyNMMS's answer over B is NMMS derivability over that larger base,
  not over B;
* Lean over B itself agrees with the stdlib reference implementation of the
  chapter's rules (`nmms_reference.py`), and the harness counts how often
  pyNMMS's added Containment changes the verdict ("containment_changed").

What each case does.
1. Generate a base over a small atom pool, with EXACT, MONOTONE and GUARDED
   entries, through pyNMMS's own `MaterialBase.add_consequence`, and send
   Lean the base's `to_dict()` serialization: once as it is (B), once with
   Containment added (B+CO).
2. Generate a sequent of random formulas, rendered in pyNMMS's surface
   syntax. pyNMMS parses the strings; the formula trees sent to Lean are
   built from pyNMMS's parse (and also compared with the generator's tree, a
   cross-check of the parser). The Lean side receives the sides in shuffled
   order with random duplicates, to exercise the "sides are sets" claim.
3. Ask pyNMMS twice: a fresh reasoner, and a reasoner with
   `persistent_cache=True` shared by all queries on the same base (this
   exercises the memo cache across queries).
4. When pyNMMS says "derivable", rebuild a proof-tree certificate from
   pyNMMS's own trace (which rule it applied to which sentence, which leaves
   it judged axioms) and have the Lean checker verify it over B+CO. A leaf
   that pyNMMS judged an axiom only because its sides share a sentence is not
   an NMMS axiom unless it is an atomic base sequent, so the harness replaces
   each non-atomic such leaf by its full decomposition, which the checker
   then verifies leaf by leaf.
5. When Lean says "not derivable" (over B or over B+CO), it also builds a
   one-branch refutation and checks it with its proved-sound refutation
   checker (`NMMS.refute`); the harness counts accepted, rejected and
   missing refutations.
6. Invertibility probes: for each complex sentence on either side, compare
   the conclusion's derivability with the derivability of all that rule's
   premises (computed by `premises`).
   a. NMMS over B, by Lean: each premise is sent to nmms-lean over B, with
      no certificate, and compared with Lean's verdict on the conclusion
      over B. Every rule is invertible (`NMMS.invertibility`), so they must
      agree ("nmms_invert_checks", "nmms_invert_fail", records
      "nmms-invertibility"). Each distinct premise is asked once per base.
   b. By pyNMMS (the shared reasoner), which tests invertibility over B plus
      Containment, not over B ("pynmms_invert_checks", "pynmms_invert_fail",
      records "pynmms-invertibility").
   Invertibility is what makes the one-branch refutations of step 5 sound.

The summary. "pynmms_derivable" and "pynmms_underivable" count pyNMMS's
verdicts over B, i.e. derivability over B plus Containment; "nmms_derivable"
counts the cases Lean derives over B itself, i.e. NMMS derivability from the
supplied base. "disagree" compares pyNMMS with Lean over B+CO, "ref_disagree"
Lean over B with the reference, and "containment_changed" counts the cases
where pyNMMS's verdict and Lean's over B differ. Certificates ("certs_*") are
checked over B+CO.

Run (from the repository root, after `lake build`):
  <pyNMMS venv>/bin/python -I difftest/difftest.py [--cases N] [--seed S]
It prints a summary (counts and timings) and writes every disagreement,
timeout or failed probe to difftest/disagreements.jsonl. A case with a Lean
query that takes longer than --timeout seconds is counted in "lean_timeout"
and recorded as "lean-timeout" (not as a disagreement): "timed_out" names the
queries ("B+CO", "B", or "probe" with the probe queries under "probe"),
"lean_ant"/"lean_con" are the sides as sent and "cert_nodes" is the size of
the certificate sent over B+CO. The Lean process is then restarted.
difftest/rerun_timeouts.py replays such queries with a longer limit.
"""

from __future__ import annotations

import argparse
import json
import random
import select
import subprocess
import time
import sys
from pathlib import Path

from pynmms.base import MaterialBase
from pynmms.reasoner import NMMSReasoner
from pynmms.robustness import EXACT, MONOTONE, exclusion, guarded
from pynmms.sequent import Sequent
from pynmms.syntax import ATOM, CONJ, DISJ, IMPL, NEG, Sentence, parse_sentence

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import nmms_reference as ref  # noqa: E402  (stdlib-only, in this directory)

LEAN_EXE = HERE.parent / ".lake" / "build" / "bin" / "nmms-lean"

ATOMS = ["p", "q", "r", "s"]

# --- generation -----------------------------------------------------------


def gen_formula(rng: random.Random, depth: int):
    """A formula as a tuple tree: ("atom", name) | ("neg", f) | (op, f, g)."""
    if depth == 0 or rng.random() < 0.35:
        return ("atom", rng.choice(ATOMS))
    op = rng.choice(["neg", "conj", "disj", "impl"])
    if op == "neg":
        return ("neg", gen_formula(rng, depth - 1))
    return (op, gen_formula(rng, depth - 1), gen_formula(rng, depth - 1))


def render(f) -> str:
    """pyNMMS surface syntax, fully parenthesized (as `str(Sentence)`)."""
    if f[0] == "atom":
        return f[1]
    if f[0] == "neg":
        return "~" + render(f[1])
    sym = {"conj": "&", "disj": "|", "impl": "->"}[f[0]]
    return f"({render(f[1])} {sym} {render(f[2])})"


def subset(rng: random.Random, lo: int, hi: int) -> list[str]:
    return rng.sample(ATOMS, rng.randint(lo, hi))


def gen_base(rng: random.Random) -> MaterialBase:
    base = MaterialBase(language=set(ATOMS))
    for _ in range(rng.randint(0, 4)):
        ant, con = subset(rng, 0, 2), subset(rng, 0, 2)
        k = rng.random()
        if k < 0.5:
            rob = EXACT
        elif k < 0.7:
            rob = MONOTONE
        else:
            pairs = []
            for _ in range(rng.randint(0, 2)):
                x, y = subset(rng, 0, 2), subset(rng, 0, 1)
                if x or y:
                    pairs.append(exclusion(x, y))
            rob = guarded(subset(rng, 0, 1), subset(rng, 0, 1), pairs)
        base.add_consequence(frozenset(ant), frozenset(con), rob)
    return base


# --- conversion -----------------------------------------------------------


def tree_of_sentence(s: Sentence):
    if s.type == ATOM:
        return ("atom", s.name)
    if s.type == NEG:
        return ("neg", tree_of_sentence(s.sub))
    return (s.type, tree_of_sentence(s.left), tree_of_sentence(s.right))


def to_json(t):
    if t[0] == "atom":
        return {"atom": t[1]}
    if t[0] == "neg":
        return {"neg": to_json(t[1])}
    return {t[0]: [to_json(t[1]), to_json(t[2])]}


def sides_json(seq: Sequent) -> tuple[list, list]:
    """The two sides of a pyNMMS sequent as formula trees for nmms-lean
    (atoms, then complex sentences in text order)."""
    def side(atoms, complex_):
        return ([to_json(("atom", a)) for a in sorted(atoms)]
                + [to_json(tree_of_sentence(s)) for s in sorted(complex_, key=str)])
    return side(seq.gamma_atoms, seq.gamma_complex), side(seq.delta_atoms, seq.delta_complex)


# --- certificates from pyNMMS traces ---------------------------------------


def premises(seq: Sequent, side: str, s: Sentence) -> list[Sequent]:
    """The premises pyNMMS's rule computes (copied from reasoner.py)."""
    if side == "L":
        rest = seq.without_left(s)
        if s.type == NEG:
            return [rest.with_right(s.sub)]
        a, b = s.left, s.right
        if s.type == IMPL:
            return [rest.with_right(a), rest.with_left(b), rest.with_left(b).with_right(a)]
        if s.type == CONJ:
            return [rest.with_left(a, b)]
        return [rest.with_left(a), rest.with_left(b), rest.with_left(a, b)]
    rest = seq.without_right(s)
    if s.type == NEG:
        return [rest.with_left(s.sub)]
    a, b = s.left, s.right
    if s.type == IMPL:
        return [rest.with_left(a).with_right(b)]
    if s.type == CONJ:
        return [rest.with_right(a), rest.with_right(b), rest.with_right(a, b)]
    return [rest.with_right(a, b)]


def full_decomposition(seq: Sequent) -> dict:
    """A certificate that decomposes every complex sentence (first left, then
    right, in text order) down to atomic leaves, each sent as an axiom leaf.
    Over a base with Containment it checks whenever the sides share a
    sentence (`NMMS.overlap_derivable`); the Lean checker verifies it."""
    for side, group in (("L", seq.gamma_complex), ("R", seq.delta_complex)):
        for s in sorted(group, key=str):
            return {"side": side, "principal": to_json(tree_of_sentence(s)),
                    "premises": [full_decomposition(p) for p in premises(seq, side, s)]}
    return {"ax": True}


def cert_from_trace(root: Sequent, entries) -> dict | None:
    """Rebuild a proof tree from pyNMMS's trace.

    The trace records every axiom leaf and every rule attempt, but not cache
    hits, so the tree is rebuilt by sequent: a sequent is proved if pyNMMS
    recorded it as an axiom, or recorded a rule attempt on it whose premises
    are all proved. Only pyNMMS's own choices are used, except that a
    non-atomic leaf pyNMMS accepted by its shared-sentence shortcut is
    expanded by `full_decomposition`.
    """
    axioms = {e.sequent for e in entries if e.kind == "AXIOM"}
    attempts: dict[Sequent, list] = {}
    for e in entries:
        if e.kind == "RULE":
            attempts.setdefault(e.sequent, []).append((e.rule[0], e.principal))
    memo: dict[Sequent, dict | None] = {}

    def build(seq: Sequent):
        if seq in memo:
            return memo[seq]
        memo[seq] = None
        out = None
        if seq in axioms:
            out = full_decomposition(seq)
        else:
            for side, s in attempts.get(seq, ()):
                subs = [build(p) for p in premises(seq, side, s)]
                if all(c is not None for c in subs):
                    out = {"side": side, "principal": to_json(tree_of_sentence(s)),
                           "premises": subs}
                    break
        memo[seq] = out
        return out

    return build(root)


def cert_size(c) -> int:
    if c is None:
        return 0
    if "ax" in c:
        return 1
    return 1 + sum(cert_size(p) for p in c["premises"])


# --- main -------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=3000)
    ap.add_argument("--seed", type=int, default=20261012)
    ap.add_argument("--per-base", type=int, default=3)
    ap.add_argument("--depth", type=int, default=3, help="maximum formula depth")
    ap.add_argument("--width", type=int, default=3, help="maximum sentences per side")
    ap.add_argument("--timeout", type=float, default=20.0,
                    help="seconds to wait for one Lean answer")
    args = ap.parse_args()
    rng = random.Random(args.seed)

    def start_lean():
        # Expanded certificates (see step 4) can exceed the default 4 MiB line cap.
        return subprocess.Popen([str(LEAN_EXE), "--max-line-bytes", str(1 << 28)],
                                stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)

    lean = start_lean()
    times = {"lean_max_s": 0.0, "py_max_s": 0.0, "lean_total_s": 0.0, "py_total_s": 0.0}

    def ask_lean(q: dict) -> dict | None:
        """Send one query; None if Lean does not answer within the timeout
        (the process is then restarted)."""
        nonlocal lean
        t0 = time.monotonic()
        lean.stdin.write(json.dumps(q) + "\n")
        lean.stdin.flush()
        ready, _, _ = select.select([lean.stdout], [], [], args.timeout)
        if not ready:
            lean.kill()
            lean.wait()
            lean = start_lean()
            return None
        out = json.loads(lean.stdout.readline())
        dt = time.monotonic() - t0
        times["lean_max_s"] = max(times["lean_max_s"], dt)
        times["lean_total_s"] += dt
        return out

    # "pynmms_*" counts are pyNMMS's verdicts (over B plus Containment);
    # "nmms_derivable" is Lean over B, NMMS derivability from the supplied base.
    stats = dict(cases=0, pynmms_derivable=0, pynmms_underivable=0, nmms_derivable=0,
                 disagree=0, cache_disagree=0, parse_mismatch=0, lean_error=0,
                 certs_built=0, certs_missing=0, certs_ok=0, certs_rejected=0, cert_nodes=0,
                 pynmms_invert_checks=0, pynmms_invert_fail=0, nmms_invert_checks=0,
                 nmms_invert_fail=0, lean_timeout=0, refute_ok=0, refute_rejected=0,
                 refute_missing=0, refute_steps=0, ref_disagree=0, containment_changed=0)
    bad = []
    case_id = 0
    while case_id < args.cases:
        base = gen_base(rng)
        shared = NMMSReasoner(base, persistent_cache=True)
        bdict = base.to_dict()
        bdict_co = ref.with_containment(bdict)
        ref_prove = ref.make_prover(ref.Base(bdict))
        over_b: dict = {}   # Lean's verdicts over B on probe premises (step 6a)
        for _ in range(args.per_base):
            if case_id >= args.cases:
                break
            case_id += 1
            ant = [gen_formula(rng, rng.randint(0, args.depth))
                   for _ in range(rng.randint(0, args.width))]
            con = [gen_formula(rng, rng.randint(0, args.depth))
                   for _ in range(rng.randint(0, args.width))]
            ant_s, con_s = sorted({render(f) for f in ant}), sorted({render(f) for f in con})
            # Parser cross-check: pyNMMS's parse must give back the generated tree.
            gen_trees = {render(f): f for f in ant + con}
            parsed = {s: tree_of_sentence(parse_sentence(s)) for s in ant_s + con_s}
            for s, t in parsed.items():
                if t != gen_trees[s]:
                    stats["parse_mismatch"] += 1
                    bad.append({"id": case_id, "kind": "parse", "text": s})
            t0 = time.monotonic()
            res = NMMSReasoner(base).derives(ant_s, con_s)
            dt = time.monotonic() - t0
            times["py_max_s"] = max(times["py_max_s"], dt)
            times["py_total_s"] += dt
            py = res.derivable
            py_shared = shared.query(ant_s, con_s)
            if py_shared != py:
                stats["cache_disagree"] += 1
                bad.append({"id": case_id, "kind": "cache", "ant": ant_s, "con": con_s,
                            "fresh": py, "shared": py_shared, "base": bdict})
            # Lean gets shuffled sides with random duplicates.
            lant = [parsed[s] for s in ant_s] + [parsed[s] for s in ant_s if rng.random() < 0.3]
            lcon = [parsed[s] for s in con_s] + [parsed[s] for s in con_s if rng.random() < 0.3]
            rng.shuffle(lant)
            rng.shuffle(lcon)
            q = {"id": case_id, "base": bdict_co, "antecedent": [to_json(t) for t in lant],
                 "consequent": [to_json(t) for t in lcon]}
            cert, nodes = None, None
            seq = Sequent.from_strings(ant_s, con_s)
            if py:
                cert = cert_from_trace(seq, res.entries)
                if cert is None:
                    stats["certs_missing"] += 1
                    bad.append({"id": case_id, "kind": "cert-missing", "ant": ant_s, "con": con_s})
                else:
                    nodes = cert_size(cert)
                    stats["certs_built"] += 1
                    stats["cert_nodes"] += nodes
                    q["cert"] = cert
            out = ask_lean(q)
            # The same sequent over B itself (no Containment): NMMS proper.
            out_b = ask_lean({**q, "base": bdict, "cert": None})
            stats["cases"] += 1
            # What difftest/rerun_timeouts.py needs to replay the timed-out queries
            # (it rebuilds the certificate from pyNMMS rather than reading it).
            timeout_rec = {"id": case_id, "kind": "lean-timeout",
                           "timed_out": [k for k, o in (("B+CO", out), ("B", out_b)) if o is None],
                           "ant": ant_s, "con": con_s,
                           "lean_ant": q["antecedent"], "lean_con": q["consequent"],
                           "connectives": res.connectives, "pynmms": py,
                           "pynmms_nodes": res.nodes, "cert_nodes": nodes, "base": bdict}
            if timeout_rec["timed_out"]:
                stats["lean_timeout"] += 1
                bad.append(timeout_rec)
                continue
            if "error" in out or "error" in out_b:
                stats["lean_error"] += 1
                bad.append({"id": case_id, "kind": "lean-error",
                            "error": out.get("error") or out_b.get("error")})
                continue
            want_b = ref_prove(frozenset(ref.freeze(to_json(t)) for t in lant),
                               frozenset(ref.freeze(to_json(t)) for t in lcon))
            stats["nmms_derivable"] += out_b["derivable"]
            if out_b["derivable"] != want_b:
                stats["ref_disagree"] += 1
                bad.append({"id": case_id, "kind": "reference", "ant": ant_s, "con": con_s,
                            "reference": want_b, "lean": out_b["derivable"], "base": bdict})
            if out_b["derivable"] != py:
                stats["containment_changed"] += 1
            stats["pynmms_derivable" if py else "pynmms_underivable"] += 1
            if out["derivable"] != py:
                stats["disagree"] += 1
                bad.append({"id": case_id, "kind": "verdict", "ant": ant_s, "con": con_s,
                            "pynmms": py, "lean": out["derivable"], "base": bdict,
                            "lean_base": bdict_co})
            if cert is not None:
                if out["cert_ok"]:
                    stats["certs_ok"] += 1
                else:
                    stats["certs_rejected"] += 1
                    bad.append({"id": case_id, "kind": "cert-rejected", "ant": ant_s,
                                "con": con_s, "cert": cert, "base": bdict_co})
            # One-branch refutation (built and checked by Lean) for "not derivable".
            for o, b in ((out, bdict_co), (out_b, bdict)):
                if o["derivable"]:
                    continue
                if o.get("refute_ok") is True:
                    stats["refute_ok"] += 1
                    stats["refute_steps"] += o.get("refute_len") or 0
                elif o.get("refute_len") is None:
                    stats["refute_missing"] += 1
                    bad.append({"id": case_id, "kind": "refute-missing", "ant": ant_s,
                                "con": con_s, "base": b})
                else:
                    stats["refute_rejected"] += 1
                    bad.append({"id": case_id, "kind": "refute-rejected", "ant": ant_s,
                                "con": con_s, "base": b})
            # Invertibility probe of NMMS over B, by Lean (step 6a).
            probe_timeouts = []
            for side, group in (("L", seq.gamma_complex), ("R", seq.delta_complex)):
                for s in sorted(group, key=str):
                    verdicts = []
                    for p in premises(seq, side, s):
                        key = (frozenset(p.gamma_atoms), p.gamma_complex,
                               frozenset(p.delta_atoms), p.delta_complex)
                        if key not in over_b:
                            pant, pcon = sides_json(p)
                            o = ask_lean({"id": case_id, "base": bdict,
                                          "antecedent": pant, "consequent": pcon})
                            if o is None:
                                probe_timeouts.append({"side": side, "principal": str(s),
                                                       "lean_ant": pant, "lean_con": pcon})
                            elif "error" in o:
                                stats["lean_error"] += 1
                                bad.append({"id": case_id, "kind": "lean-error",
                                            "query": "probe", "error": o["error"]})
                            else:
                                over_b[key] = o["derivable"]
                        verdicts.append(over_b.get(key))
                    if None in verdicts:
                        continue
                    prem = all(verdicts)
                    stats["nmms_invert_checks"] += 1
                    if prem != out_b["derivable"]:
                        stats["nmms_invert_fail"] += 1
                        bad.append({"id": case_id, "kind": "nmms-invertibility", "ant": ant_s,
                                    "con": con_s, "side": side, "principal": str(s),
                                    "conclusion": out_b["derivable"], "premises": prem,
                                    "base": bdict})
            if probe_timeouts:
                stats["lean_timeout"] += 1
                bad.append({**timeout_rec, "timed_out": ["probe"], "probe": probe_timeouts})
            # Invertibility probe by pyNMMS, i.e. over B plus Containment (step 6b).
            for side, group in (("L", seq.gamma_complex), ("R", seq.delta_complex)):
                for s in group:
                    prem = all(shared.derives_sequent(p).derivable
                               for p in premises(seq, side, s))
                    stats["pynmms_invert_checks"] += 1
                    if prem != py:
                        stats["pynmms_invert_fail"] += 1
                        bad.append({"id": case_id, "kind": "pynmms-invertibility", "ant": ant_s,
                                    "con": con_s, "side": side, "principal": str(s),
                                    "conclusion": py, "premises": prem, "base": bdict})
    lean.stdin.close()
    lean.wait()
    (HERE / "disagreements.jsonl").write_text("".join(json.dumps(b) + "\n" for b in bad))
    print(json.dumps({"seed": args.seed, "depth": args.depth, "width": args.width,
                      **stats, **{k: round(v, 3) for k, v in times.items()}}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
