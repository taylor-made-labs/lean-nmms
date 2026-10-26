"""Check the executable against a finite forward transcription of NMMS.

Source: Hlobil and Brandom, Reasons for Logic, Logic for Reasons, chapter 3,
printed pp. 108–111: atomic base axioms, the eight rules, and set contexts.
Author-hosted chapter (a course copy, not authenticated as the final edition):
https://sites.pitt.edu/~rbrandom/Courses/2024%20Philosophy%20of%20Language/Texts/RLLR%20Chapter%203.pdf

This oracle takes the least forward closure of the raw atomic axioms. Every
rule context ranges over every subset of the formula palette, including
contexts that already contain the principal. It neither removes principals
nor assumes invertibility, and imports no search or rule helpers from Lean,
pyNMMS, or difftest/nmms_reference.py.

The palettes are finite and closed under subformulas. The source rules do
not introduce new formulas when followed from a conclusion toward its
premises, so forward saturation covers all derivations of roots in a
palette. This is exhaustive only for the explicitly enumerated finite
universes; it is not a proof for arbitrary formulas or base relations.

After `lake build`: python3 -B -m unittest -v tests.test_nmms_forward
Set NMMS_LEAN_EXE to test another executable. Stdlib only.
"""

from collections import deque
import itertools
import json
import os
from pathlib import Path
import random
import subprocess
import unittest


ROOT = Path(__file__).resolve().parents[1]
EXE = Path(os.environ.get("NMMS_LEAN_EXE", ROOT / ".lake/build/bin/nmms-lean"))
TIMEOUT_SECONDS = 180
MAX_FAILURE_EXAMPLES = 3

# Immutable formula trees: ("atom", name), ("neg", A), or (connective, A, B).
P, Q, R = ("atom", "p"), ("atom", "q"), ("atom", "r")
ONE_ATOM = (P, ("neg", P), ("conj", P, P), ("disj", P, P), ("impl", P, P))
TWO_ATOMS = (P, Q, ("neg", P), ("conj", P, Q), ("disj", P, Q), ("impl", P, Q))


def formula_json(formula):
    tag, *args = formula
    if tag == "atom":
        return {tag: args[0]}
    if tag == "neg":
        return {tag: formula_json(args[0])}
    return {tag: [formula_json(arg) for arg in args]}


class ForwardNMMS:
    """All book-rule instances over a finite, subformula-closed palette.

    A side is a bit set of formulas. A sequent is the integer G * side_count
    + D, so both empty sides and every context with a retained principal are
    represented. Rule instances are (distinct premise sequents, conclusion).
    """

    def __init__(self, formulas):
        self.formulas = tuple(formulas)
        if len(set(formulas)) != len(formulas):
            raise ValueError("the formula palette must have no duplicates")
        self.bits = {formula: 1 << i for i, formula in enumerate(formulas)}
        for formula in formulas:
            if formula[0] not in ("atom", "neg", "conj", "disj", "impl"):
                raise ValueError(f"unknown connective: {formula[0]}")
            if formula[0] != "atom" and any(arg not in self.bits for arg in formula[1:]):
                raise ValueError("the formula palette must be closed under subformulas")
        self.side_count = 1 << len(formulas)
        self.state_count = self.side_count ** 2
        self.atoms = tuple(formula for formula in formulas if formula[0] == "atom")
        atomic_sides = [
            sum(self.bits[atom] for i, atom in enumerate(self.atoms) if mask & (1 << i))
            for mask in range(1 << len(self.atoms))
        ]
        self.atomic_states = tuple(
            self.encode(G, D) for G in atomic_sides for D in atomic_sides
        )
        self.rules = []
        self.users = [[] for _ in range(self.state_count)]
        self._enumerate_rules()

    def encode(self, G, D):
        return G * self.side_count + D

    def sequent(self, antecedent, consequent):
        def side(formulas):
            return sum(self.bits[formula] for formula in set(formulas))
        return self.encode(side(antecedent), side(consequent))

    def _add_rule(self, premises, conclusion):
        # Repeated top sequents impose the same obligation once. In particular
        # A and B may be equal; this does not remove a distinct third premise.
        premises = tuple(sorted(set(premises)))
        index = len(self.rules)
        self.rules.append((premises, conclusion))
        for premise in premises:
            self.users[premise].append(index)

    def _enumerate_rules(self):
        seq = self.encode
        for formula in self.formulas:
            tag = formula[0]
            if tag == "atom":
                continue
            principal = self.bits[formula]
            A = self.bits[formula[1]]
            B = self.bits[formula[2]] if len(formula) == 3 else None
            # G and D are the rule contexts, not sides with a principal erased.
            for G, D in itertools.product(range(self.side_count), repeat=2):
                if tag == "neg":
                    left = [seq(G, D | A)]
                    right = [seq(G | A, D)]
                elif tag == "conj":
                    left = [seq(G | A | B, D)]
                    right = [seq(G, D | A), seq(G, D | B), seq(G, D | A | B)]
                elif tag == "disj":
                    left = [seq(G | A, D), seq(G | B, D), seq(G | A | B, D)]
                    right = [seq(G, D | A | B)]
                else:  # implication
                    left = [seq(G, D | A), seq(G | B, D), seq(G | B, D | A)]
                    right = [seq(G | A, D | B)]
                self._add_rule(left, seq(G | principal, D))
                self._add_rule(right, seq(G, D | principal))

    def closure(self, axioms):
        """Least forward fixed point; circular rules cannot justify themselves."""
        reached = set(axioms)
        if not reached.issubset(self.atomic_states):
            raise ValueError("only atomic sequents may be supplied as axioms")
        pending = deque(sorted(reached))
        remaining = [len(premises) for premises, _ in self.rules]
        while pending:
            premise = pending.popleft()
            for index in self.users[premise]:
                remaining[index] -= 1
                if remaining[index] == 0:
                    conclusion = self.rules[index][1]
                    if conclusion not in reached:
                        reached.add(conclusion)
                        pending.append(conclusion)
        return reached

    def side_json(self, mask):
        return [formula_json(f) for f in self.formulas if mask & self.bits[f]]

    def base_json(self, axioms):
        entries = []
        for state in axioms:
            G, D = divmod(state, self.side_count)
            entries.append({
                "antecedent": [a[1] for a in self.atoms if G & self.bits[a]],
                "consequent": [a[1] for a in self.atoms if D & self.bits[a]],
                "robustness": "exact",
            })
        return {"language": [a[1] for a in self.atoms], "consequences": entries}


class ForwardOracleChecks(unittest.TestCase):
    """Small source-based discriminators for accidental changes to the oracle."""

    def test_raw_atomic_relation_and_empty_base_are_preserved(self):
        model = ForwardNMMS(ONE_ATOM)
        self.assertEqual(model.closure([]), set())
        for mask in range(16):
            axioms = {state for i, state in enumerate(model.atomic_states) if mask & (1 << i)}
            with self.subTest(base_mask=mask):
                self.assertEqual(model.closure(axioms).intersection(model.atomic_states), axioms)

    def test_each_distinct_third_premise_is_required(self):
        cases = (
            ("disj", [([P], [R]), ([Q], [R]), ([P, Q], [R])], "L"),
            ("conj", [([R], [P]), ([R], [Q]), ([R], [P, Q])], "R"),
            ("impl", [([], [P, R]), ([Q], [R]), ([Q], [P, R])], "L"),
        )
        for tag, premises, side in cases:
            formula = (tag, P, Q)
            model = ForwardNMMS((P, Q, R, formula))
            axioms = [model.sequent(G, D) for G, D in premises]
            target = model.sequent([formula], [R]) if side == "L" else model.sequent([R], [formula])
            with self.subTest(rule=f"{side} {tag}"):
                self.assertNotIn(target, model.closure(axioms[:2]))
                self.assertIn(target, model.closure(axioms))

    def test_contexts_can_retain_the_principal(self):
        neg = ("neg", P)
        model = ForwardNMMS((P, neg))
        left = ((model.sequent([neg], [P]),), model.sequent([neg], []))
        right = ((model.sequent([P], [neg]),), model.sequent([], [neg]))
        self.assertIn(left, model.rules)
        self.assertIn(right, model.rules)

    def test_palette_must_be_closed_under_subformulas(self):
        with self.assertRaisesRegex(ValueError, "subformulas"):
            ForwardNMMS((P, ("conj", P, Q)))


class ExecutableAgainstForwardRules(unittest.TestCase):
    def compare(self, label, formulas, base_masks, states):
        self.assertTrue(EXE.is_file(), f"run lake build first, or set NMMS_LEAN_EXE: {EXE}")
        model = ForwardNMMS(formulas)
        queries, expected = [], []
        for base_mask in base_masks:
            axioms = [state for i, state in enumerate(model.atomic_states) if base_mask & (1 << i)]
            reached = model.closure(axioms)
            base = model.base_json(axioms)
            for state in states:
                G, D = divmod(state, model.side_count)
                queries.append({
                    "id": f"{label}:{base_mask}:{state}", "base": base,
                    "antecedent": model.side_json(G), "consequent": model.side_json(D),
                })
                expected.append(state in reached)
        request = "".join(json.dumps(q, separators=(",", ":")) + "\n" for q in queries)
        try:
            process = subprocess.run(
                [str(EXE)], input=request, text=True, capture_output=True,
                timeout=TIMEOUT_SECONDS,
            )
        except subprocess.TimeoutExpired:
            self.fail(f"{label}: {len(queries)} queries exceeded {TIMEOUT_SECONDS}s")
        self.assertEqual(process.returncode, 0, f"{label}: stderr: {process.stderr[:2000]}")
        lines = process.stdout.splitlines()
        self.assertEqual(len(lines), len(queries),
                         f"{label}: expected one response per query; stderr: {process.stderr[:1000]}")
        failures, examples = 0, []
        for query, want, line in zip(queries, expected, lines):
            try:
                response = json.loads(line)
            except json.JSONDecodeError:
                self.fail(f"{label}, query {query['id']}: invalid JSON response: {line[:500]}")
            good = isinstance(response, dict) and "error" not in response
            if good:
                good = (response.get("id") == query["id"]
                        and response.get("derivable") is want
                        and "cert_ok" in response and response["cert_ok"] is None)
                if want:
                    good = good and "refute_ok" in response and response["refute_ok"] is None
                    good = good and "refute_len" in response and response["refute_len"] is None
                else:
                    good = good and response.get("refute_ok") is True
                    length = response.get("refute_len")
                    good = good and type(length) is int and length >= 0
            if not good:
                failures += 1
                if len(examples) < MAX_FAILURE_EXAMPLES:
                    examples.append(f"expected derivable={want}; query={json.dumps(query)}; "
                                    f"response={line[:1000]}")
        self.assertEqual(failures, 0,
                         f"{label}: {failures}/{len(queries)} mismatches\n" + "\n".join(examples))

    def test_exhaustive_one_atom_16384_queries(self):
        # Four possible atomic sequents, hence sixteen arbitrary raw bases.
        # Five formulas give 32 sides and 1,024 pairs of sides per base.
        self.compare("one-atom", ONE_ATOM, range(16), range(1024))

    def test_deterministic_two_atom_sample(self):
        rng = random.Random(2401)
        model = ForwardNMMS(TWO_ATOMS)
        states = sorted(set(model.atomic_states) | set(rng.sample(range(model.state_count), 256)))
        # Empty/full, singleton, sparse and seeded arbitrary raw relations.
        base_masks = [0, 65535, 1, 32768, 0x8421, 0x1248]
        base_masks.extend(rng.randrange(65536) for _ in range(10))
        self.compare("two-atoms", TWO_ATOMS, base_masks, states)


if __name__ == "__main__":
    unittest.main(verbosity=2)
