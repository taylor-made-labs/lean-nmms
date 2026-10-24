"""A small reference implementation of NMMS, independent of the Lean code.

It follows the rules of Hlobil and Brandom (2025, ch. 3, pp. 108-111)
directly: sequents are pairs of frozensets of formulas, the axioms are the
atomic sequents in the supplied base and nothing else (no Containment), and
a sequent is derivable when some rule applied to some complex sentence has
all its premises derivable (root-first search over every choice, memoized).
The premises remove the principal sentence from its side; the Lean theorem
`NMMS.invertibility` shows the book's other instances (context keeping the
principal sentence) add nothing.

Formulas are JSON trees as `nmms-lean` reads them: {"atom": "p"},
{"neg": F}, {"conj": [F, F]}, {"disj": [F, F]}, {"impl": [F, F]}. Bases are
pyNMMS `MaterialBase.to_dict()` dicts (EXACT, MONOTONE, GUARDED entries).

Stdlib only. Used by tests/test_nmms_rules.py and difftest/difftest.py.
"""

from __future__ import annotations

import json
import random
from functools import lru_cache


# --- formulas ---------------------------------------------------------------

def freeze(f):
    """JSON tree -> hashable tuple tree: ("atom", n) | ("neg", f) | (op, f, g)."""
    if "atom" in f:
        return ("atom", f["atom"])
    if "neg" in f:
        return ("neg", freeze(f["neg"]))
    for op in ("conj", "disj", "impl"):
        if op in f:
            a, b = f[op]
            return (op, freeze(a), freeze(b))
    raise ValueError(f"not a formula: {f!r}")


def thaw(t):
    """Tuple tree -> JSON tree."""
    if t[0] == "atom":
        return {"atom": t[1]}
    if t[0] == "neg":
        return {"neg": thaw(t[1])}
    return {t[0]: [thaw(t[1]), thaw(t[2])]}


def is_atom(t) -> bool:
    return t[0] == "atom"


def atoms(t):
    if t[0] == "atom":
        return {t[1]}
    if t[0] == "neg":
        return atoms(t[1])
    return atoms(t[1]) | atoms(t[2])


# --- the base -----------------------------------------------------------------

def _atoms(v, what: str) -> frozenset:
    """A list of atom names (a string or any other value is refused)."""
    if not isinstance(v, list) or not all(isinstance(a, str) for a in v):
        raise ValueError(f"{what} must be a list of strings")
    return frozenset(v)


def _robustness(rob):
    """An entry's "robustness", read and refused as nmms-lean does (see the
    header of Main.lean; pyNMMS's `Robustness.from_json` accepts every value
    accepted here and reads it the same way, and also reads a few refused
    here, which that header lists, among them a string or an object where a
    list of atoms is expected): absent or null is EXACT, a
    string is a kind, an object has "kind" (default "exact") and "unless"
    (absent or null: no defeaters, otherwise an object, type-checked for
    every kind). An exclusion pair with no atom, and defeaters on an EXACT or
    MONOTONE entry, are refused. Returns (kind, (left, right, pairs))."""
    if rob is None:
        kind, unless = "exact", None
    elif isinstance(rob, str):
        kind, unless = rob, None
    elif isinstance(rob, dict):
        kind, unless = rob.get("kind", "exact"), rob.get("unless")
        if not isinstance(kind, str):
            raise ValueError("robustness kind must be a string")
    else:
        raise ValueError("robustness must be a string or an object")
    if unless is None:
        unless = {}
    if not isinstance(unless, dict):
        raise ValueError("unless must be an object")
    left = _atoms(unless.get("antecedent", []), "unless.antecedent")
    right = _atoms(unless.get("consequent", []), "unless.consequent")
    if not isinstance(unless.get("pairs", []), list):
        raise ValueError("unless.pairs must be an array")
    pairs = []
    for p in unless.get("pairs", []):
        if not isinstance(p, dict):
            raise ValueError("unless.pairs entry must be an object")
        x = _atoms(p.get("antecedent", []), "unless.pairs antecedent")
        y = _atoms(p.get("consequent", []), "unless.pairs consequent")
        if not x and not y:
            raise ValueError("an exclusion pair needs at least one atom")
        pairs.append((x, y))
    if kind not in ("exact", "monotone", "guarded"):
        raise ValueError(f"unknown robustness kind {kind}")
    if kind != "guarded" and (left or right or pairs):
        raise ValueError(f"defeaters (unless) are only meaningful for guarded entries, not {kind}")
    return kind, (left, right, tuple(pairs))


class Base:
    """The base relation of a pyNMMS base dict, on pairs of sets of atom names.
    A malformed entry raises ValueError (see `_robustness`)."""

    def __init__(self, bdict: dict):
        self.entries = []
        if not isinstance(bdict.get("consequences"), list):
            raise ValueError('base needs a "consequences" array')
        for e in bdict["consequences"]:
            if not isinstance(e, dict):
                raise ValueError("a base entry must be an object")
            ant = _atoms(e.get("antecedent"), "antecedent")
            con = _atoms(e.get("consequent"), "consequent")
            kind, guard = _robustness(e.get("robustness"))
            self.entries.append((ant, con, kind, guard))

    def contains(self, X: frozenset, Y: frozenset) -> bool:
        for ant, con, kind, (left, right, pairs) in self.entries:
            if kind == "exact":
                if ant == X and con == Y:
                    return True
            elif ant <= X and con <= Y:
                if kind == "monotone":
                    return True
                if kind == "guarded" and not (left & X) and not (right & Y) and \
                        not any(x <= X and y <= Y for x, y in pairs):
                    return True
        return False


# --- the rules ------------------------------------------------------------------

def premises(G: frozenset, D: frozenset, side: str, s, keep: bool = False):
    """The premises of the rule on `s` (side "L" or "R"). With keep=True the
    context still contains `s` (the book's other instance)."""
    if side == "L":
        g = G if keep else G - {s}
        if s[0] == "neg":
            return [(g, D | {s[1]})]
        a, b = s[1], s[2]
        if s[0] == "conj":
            return [(g | {a, b}, D)]
        if s[0] == "disj":
            return [(g | {a}, D), (g | {b}, D), (g | {a, b}, D)]
        return [(g, D | {a}), (g | {b}, D), (g | {b}, D | {a})]          # impl
    d = D if keep else D - {s}
    if s[0] == "neg":
        return [(G | {s[1]}, d)]
    a, b = s[1], s[2]
    if s[0] == "conj":
        return [(G, d | {a}), (G, d | {b}), (G, d | {a, b})]
    if s[0] == "disj":
        return [(G, d | {a, b})]
    return [(G | {a}, d | {b})]                                            # impl


def make_prover(base: Base):
    """Return derivable(G, D) for frozensets of tuple formulas."""

    @lru_cache(maxsize=None)
    def derivable(G: frozenset, D: frozenset) -> bool:
        comp = [("L", s) for s in G if not is_atom(s)] + [("R", s) for s in D if not is_atom(s)]
        if not comp:
            return base.contains(frozenset(t[1] for t in G), frozenset(t[1] for t in D))
        return any(all(derivable(*p) for p in premises(G, D, side, s)) for side, s in comp)

    return derivable


def derives(bdict: dict, antecedent, consequent) -> bool:
    """Is antecedent => consequent (JSON formula lists) derivable over bdict?"""
    G = frozenset(freeze(f) for f in antecedent)
    D = frozenset(freeze(f) for f in consequent)
    return make_prover(Base(bdict))(G, D)


def decomposition_cert(G: frozenset, D: frozenset, rng: random.Random | None = None,
                       keeps: int = 0):
    """A certificate (nmms-lean's JSON format) that fully decomposes G => D,
    always on the first complex sentence in a fixed order. It checks exactly
    when every leaf is in the base, i.e. (by invertibility) exactly when the
    sequent is derivable. With `rng`, up to `keeps` steps use the book's
    instance whose context keeps the principal sentence."""
    comp = sorted([("L", s) for s in G if not is_atom(s)] + [("R", s) for s in D if not is_atom(s)],
                  key=lambda x: (x[0], json.dumps(thaw(x[1]), sort_keys=True)))
    if not comp:
        return {"ax": True}
    side, s = comp[0]
    keep = bool(rng and keeps > 0 and rng.random() < 0.3)
    node = {"side": side, "principal": thaw(s),
            "premises": [decomposition_cert(g, d, rng, keeps - 1 if keep else keeps)
                         for g, d in premises(G, D, side, s, keep)]}
    if keep:
        node["keep"] = True
    elif rng and rng.random() < 0.2:
        node["keep"] = False
    return node


# --- random generation ----------------------------------------------------------------

def gen_formula(rng: random.Random, atoms_pool, depth: int):
    if depth == 0 or rng.random() < 0.35:
        return {"atom": rng.choice(atoms_pool)}
    op = rng.choice(["neg", "conj", "disj", "impl"])
    if op == "neg":
        return {"neg": gen_formula(rng, atoms_pool, depth - 1)}
    return {op: [gen_formula(rng, atoms_pool, depth - 1), gen_formula(rng, atoms_pool, depth - 1)]}


def gen_base(rng: random.Random, atoms_pool, max_entries: int = 5) -> dict:
    """A pyNMMS-format base with one entry per pair (as sets)."""
    seen, cons = set(), []
    for _ in range(rng.randint(0, max_entries)):
        ant = sorted(rng.sample(atoms_pool, rng.randint(0, 2)))
        con = sorted(rng.sample(atoms_pool, rng.randint(0, 2)))
        if (tuple(ant), tuple(con)) in seen:
            continue
        seen.add((tuple(ant), tuple(con)))
        k = rng.random()
        if k < 0.5:
            rob = {"kind": "exact"}
        elif k < 0.75:
            rob = {"kind": "monotone"}
        else:
            rob = {"kind": "guarded", "unless": {
                "antecedent": sorted(rng.sample(atoms_pool, rng.randint(0, 1))),
                "consequent": sorted(rng.sample(atoms_pool, rng.randint(0, 1))),
                "pairs": [{"antecedent": sorted(rng.sample(atoms_pool, rng.randint(1, 2))),
                           "consequent": sorted(rng.sample(atoms_pool, rng.randint(0, 1)))}
                          for _ in range(rng.randint(0, 1))]}}
        cons.append({"antecedent": ant, "consequent": con, "robustness": rob})
    return {"language": sorted(atoms_pool), "consequences": cons}


def with_containment(bdict: dict) -> dict:
    """The same base plus Containment for its language: a MONOTONE `a |~ a` per
    atom (an existing `a |~ a` entry becomes MONOTONE, which includes it)."""
    cons = [dict(e) for e in bdict["consequences"]]
    for a in bdict["language"]:
        for e in cons:
            if sorted(set(e["antecedent"])) == [a] and sorted(set(e["consequent"])) == [a]:
                e["robustness"] = {"kind": "monotone"}
                break
        else:
            cons.append({"antecedent": [a], "consequent": [a], "robustness": {"kind": "monotone"}})
    return {**bdict, "consequences": cons}
