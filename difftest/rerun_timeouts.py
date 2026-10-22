"""Re-run the Lean side of recorded "lean-timeout" cases with a longer limit.

Usage: <pyNMMS venv>/bin/python -I difftest/rerun_timeouts.py RECORDS.jsonl SECONDS
Each case runs in its own nmms-lean process, all in parallel; prints one line
per case: id, connectives, pyNMMS verdict, Lean verdict (or "timeout"), seconds.
"""
import json
import subprocess
import sys
import time
from pathlib import Path

from pynmms.syntax import ATOM, NEG, parse_sentence

EXE = Path(__file__).resolve().parent.parent / ".lake" / "build" / "bin" / "nmms-lean"


def tree(s):
    if s.type == ATOM:
        return {"atom": s.name}
    if s.type == NEG:
        return {"neg": tree(s.sub)}
    return {s.type: [tree(s.left), tree(s.right)]}


recs = [json.loads(l) for l in open(sys.argv[1]) if '"lean-timeout"' in l]
limit = float(sys.argv[2])
procs = []
for r in recs:
    q = {"id": r["id"], "base": r["base"],
         "antecedent": [tree(parse_sentence(s)) for s in r["ant"]],
         "consequent": [tree(parse_sentence(s)) for s in r["con"]]}
    p = subprocess.Popen([str(EXE)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    p.stdin.write(json.dumps(q) + "\n")
    p.stdin.close()
    p.stdin = None
    procs.append((r, p, time.monotonic()))
for r, p, t0 in procs:
    try:
        text, _ = p.communicate(timeout=max(1, limit - (time.monotonic() - t0)))
        verdict = json.loads(text.splitlines()[0]).get("derivable")
    except subprocess.TimeoutExpired:
        p.kill()
        verdict = "timeout"
    print(r["id"], r["connectives"], r["pynmms"], verdict, round(time.monotonic() - t0, 1),
          flush=True)
