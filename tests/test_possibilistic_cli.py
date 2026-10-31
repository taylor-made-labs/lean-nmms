"""nmms-lean's weighted queries (tracer N): "weight" per entry, "threshold" and
"degree": true. The expected answers are the ones LeanNmms/Possibilistic.lean
computes for the shared example (tests/PossibilisticExamples.lean); the
refusals are the header's rules. Run from the repository root after
`lake build`: python3 -m unittest tests.test_possibilistic_cli
"""
import json
import os
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXE = Path(os.environ.get("NMMS_LEAN_EXE", ROOT / ".lake/build/bin/nmms-lean"))


def run(queries, timeout=120):
    text = "".join(json.dumps(q) + "\n" for q in queries)
    out = subprocess.run([str(EXE)], input=text, capture_output=True, text=True, timeout=timeout)
    lines = [line for line in out.stdout.splitlines() if line.strip()]
    assert len(lines) == len(queries), (out.stdout, out.stderr)
    return [json.loads(line) for line in lines]


def entry(ant, con, weight=None, kind="exact"):
    e = {"antecedent": ant, "consequent": con, "robustness": kind}
    if weight is not None:
        e["weight"] = weight
    return e


BASE = {"language": ["p", "q", "r", "s"], "consequences": [
    entry(["p"], ["q"], "1"), entry(["p"], ["r"], "1/2"), entry(["p"], ["q", "r"], "1/2"),
    entry(["r"], ["s"], "0")]}
A = lambda a: {"atom": a}
Q_AND_R = {"conj": [A("q"), A("r")]}


def ask(base, ant, con, **extra):
    return {"id": 1, "base": base, "antecedent": ant, "consequent": con, **extra}


class WeightedQueries(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not EXE.is_file():
            raise AssertionError(f"built nmms-lean required at {EXE}")

    def test_degree_on_the_shared_example(self):
        answers = run([ask(BASE, [A("p")], [Q_AND_R], degree=True), ask(BASE, [A("p")], [A("q")], degree=True),
                       ask(BASE, [A("r")], [A("s")], degree=True), ask(BASE, [A("q")], [A("p")], degree=True)])
        self.assertEqual([a["degree"] for a in answers], ["1/2", "1/1", "0/1", None])
        for a in answers:
            self.assertEqual(set(a), {"id", "degree"})

    def test_threshold_answers_over_the_cut_and_echoes_it(self):
        answers = run([ask(BASE, [A("p")], [Q_AND_R], threshold=t) for t in ["0", "1/2", "3/4", "1"]])
        self.assertEqual([a["derivable"] for a in answers], [True, True, False, False])
        self.assertEqual([a["threshold"] for a in answers], ["0/1", "1/2", "3/4", "1/1"])
        self.assertTrue(answers[2]["refute_ok"], "the refutation is over the cut")

    def test_cut_theorem_degree_at_least_t_iff_threshold_derivable(self):
        seqs = [([A("p")], [Q_AND_R]), ([A("p")], [A("q")]), ([A("r")], [A("s")]), ([A("q")], [A("p")])]
        from fractions import Fraction
        for ant, con in seqs:
            degree = run([ask(BASE, ant, con, degree=True)])[0]["degree"]
            d = None if degree is None else Fraction(degree)
            for t in ["0", "1/8", "1/4", "1/2", "3/4", "1"]:
                with self.subTest(seq=(ant, con), t=t):
                    derivable = run([ask(BASE, ant, con, threshold=t)])[0]["derivable"]
                    self.assertEqual(derivable, d is not None and Fraction(t) <= d)

    def test_unweighted_query_unchanged(self):
        plain = {"language": BASE["language"], "consequences": [dict(e, weight=None) for e in BASE["consequences"]]}
        for e in plain["consequences"]:
            del e["weight"]
        a = run([ask(plain, [A("p")], [Q_AND_R])])[0]
        self.assertEqual(set(a), {"id", "derivable", "cert_ok", "refute_ok", "refute_len"})
        self.assertTrue(a["derivable"])

    def test_refusals(self):
        missing = {"language": BASE["language"], "consequences": BASE["consequences"][:3] + [entry(["r"], ["s"])]}
        cases = {
            "missing weight": ask(missing, [A("p")], [A("q")], degree=True),
            "weights without a weighted query": ask(BASE, [A("p")], [A("q")]),
            "both threshold and degree": ask(BASE, [A("p")], [A("q")], threshold="1/2", degree=True),
            "weight above 1": ask({"consequences": [entry(["p"], ["q"], "3/2")]}, [A("p")], [A("q")], degree=True),
            "weight as a number": ask({"consequences": [entry(["p"], ["q"], 0.5)]}, [A("p")], [A("q")], degree=True),
            "denominator 0": ask({"consequences": [entry(["p"], ["q"], "1/0")]}, [A("p")], [A("q")], degree=True),
            "bad threshold": ask(BASE, [A("p")], [A("q")], threshold="half"),
            "degree not a boolean": ask(BASE, [A("p")], [A("q")], degree="yes"),
            "too many digits": ask({"consequences": [entry(["p"], ["q"], "1" * 41 + "/" + "1" * 41)]},
                                   [A("p")], [A("q")], degree=True),
        }
        answers = dict(zip(cases, run(list(cases.values()))))
        for name, a in answers.items():
            with self.subTest(case=name):
                self.assertIn("error", a, a)
                self.assertNotIn("derivable", a)
                self.assertNotIn("degree", a)


if __name__ == "__main__":
    unittest.main()
