"""Replay the Lean queries of recorded "lean-timeout" cases with a longer limit.

Usage: <pyNMMS venv>/bin/python -I difftest/rerun_timeouts.py RECORDS.jsonl SECONDS

For each "lean-timeout" record that difftest.py wrote, this sends nmms-lean
the queries named in the record's "timed_out", as difftest.py sent them:
"B+CO" is the query over the base plus Containment, with the certificate if
difftest.py attached one; "B" is the query over the base itself; "probe" are
the invertibility-probe queries over the base (the record's "probe" list).
The base is rebuilt with pyNMMS's `MaterialBase.from_dict`, pyNMMS is rerun on
the recorded sequent, and the certificate is rebuilt from its trace by
difftest.py's own `cert_from_trace`; the sides are the recorded "lean_ant" and
"lean_con". Each query runs alone in a fresh nmms-lean, started with
difftest.py's --max-line-bytes, one after another, so the seconds compare with
difftest.py's. One line per query (probe lines in the order of "probe"): id,
base label, whether a certificate was attached, pyNMMS's verdict on the
recorded sequent (over B, i.e. derivability over B plus Containment), Lean's
verdict on that query over its base (or "timeout"), cert_ok, seconds. A
warning line says if the rebuilt base, pyNMMS verdict or certificate size
differs from the record.
"""
import json
import select
import subprocess
import sys
import time
from pathlib import Path

from pynmms.base import MaterialBase
from pynmms.reasoner import NMMSReasoner
from pynmms.sequent import Sequent

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import nmms_reference as ref  # noqa: E402
from difftest import LEAN_EXE, cert_from_trace, cert_size  # noqa: E402


def ask(q: dict, limit: float) -> tuple[dict | None, float]:
    """One query in a fresh nmms-lean: (answer, or None after `limit` seconds; seconds)."""
    lean = subprocess.Popen([str(LEAN_EXE), "--max-line-bytes", str(1 << 28)],
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    t0 = time.monotonic()
    lean.stdin.write(json.dumps(q) + "\n")
    lean.stdin.flush()
    ready, _, _ = select.select([lean.stdout], [], [], limit)
    line = lean.stdout.readline() if ready else None
    dt = time.monotonic() - t0
    lean.kill()
    lean.wait()
    lean.stdin.close()
    lean.stdout.close()
    if line is None:
        return None, dt
    return (json.loads(line) if line else {"error": f"no answer (exit {lean.returncode})"}), dt


def main() -> int:
    if len(sys.argv) != 3:
        sys.exit(__doc__.splitlines()[2])
    limit = float(sys.argv[2])
    with open(sys.argv[1]) as f:
        recs = [r for r in (json.loads(line) for line in f if '"lean-timeout"' in line)
                if r.get("kind") == "lean-timeout"]
    for r in recs:
        base = MaterialBase.from_dict(r["base"])
        bdict = base.to_dict()
        res = NMMSReasoner(base).derives(r["ant"], r["con"])
        cert = cert_from_trace(Sequent.from_strings(r["ant"], r["con"]), res.entries) \
            if res.derivable else None
        nodes = None if cert is None else cert_size(cert)
        differs = [k for k, same in (("base", bdict == r["base"]),
                                     ("pynmms", res.derivable == r["pynmms"]),
                                     ("cert_nodes", nodes == r["cert_nodes"])) if not same]
        if differs:
            print(r["id"], "warning: the replay differs from the record in", ", ".join(differs),
                  flush=True)
        q = {"id": r["id"], "base": ref.with_containment(bdict),
             "antecedent": r["lean_ant"], "consequent": r["lean_con"]}
        if cert is not None:
            q["cert"] = cert
        queries = []
        if "B+CO" in r["timed_out"]:
            queries.append(("B+CO", q))
        if "B" in r["timed_out"]:
            queries.append(("B", {**q, "base": bdict, "cert": None}))
        if "probe" in r["timed_out"]:
            queries += [("probe", {"id": r["id"], "base": bdict, "antecedent": p["lean_ant"],
                                   "consequent": p["lean_con"]}) for p in r["probe"]]
        for label, query in queries:
            out, dt = ask(query, limit)
            if out is None:
                verdict, cert_ok = "timeout", None
            else:
                verdict = out.get("derivable", "error: " + str(out.get("error")))
                cert_ok = out.get("cert_ok")
            print(r["id"], label, f"cert={query.get('cert') is not None}",
                  f"pynmms={res.derivable}", f"lean={verdict}", f"cert_ok={cert_ok}",
                  f"{dt:.1f}s", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
