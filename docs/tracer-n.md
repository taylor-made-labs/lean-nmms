# Tracer N: possibilistic weights in lean-nmms and graph-nmms

Status: **built and proved, round 1 (31 Oct 2026)**, on branch
`tests/tracer-n` in both repositories, awaiting the sized review and the
merge to main. No `sorry`; every test below passes.

## Direction (Taylor, 30 Oct)

- Uncertainty is a first-class citizen: weights inside one agent's model,
  plus each source's own uncertainty value.
- Possibilistic logic is the foundation.
- The threshold `t` can be 0.
- Lean covers the core computation at every threshold, not only the
  "true" fragment.
- The work is not held back for publish-ready research.

The plan (`records/plans/turn-13-suite-alignment/map.md`, tracer N) asks for
the cut theorem (degree = the largest `t` at which `B_t` derives, the
weakest-link rule), and `derivable_iff_valid` holding per threshold.

## Decisions (accepted by the suite PM, 31 Oct)

- **The degree is an `Option`.** With a degree in [0,1], "degree ≥ 0" would
  always hold, but `B_0` (the whole base) does not derive everything; so the
  cut theorem at `t = 0` forces `none` = no cut derives it, `some 0` =
  derivable over the whole base only. This keeps "t can be 0" meaningful: an
  entry weighted 0 takes part at threshold 0 and nowhere else.
- **The scale is ordinal.** Possibilistic logic uses only comparisons, min
  and max. `Scale W` is a decidable total preorder with `zero` and `one`;
  `Q01` (rationals in [0,1]) is the executable instance. No antisymmetry, so
  the degree is unique up to `≤` both ways. Floats are refused everywhere.
- **Weakest link is stated over selections of entries**, not proof trees:
  NMMS has no chaining, and a leaf can only be matched by different entries.
- **A source's own value combines with the holder's weight by `min`**, the
  possibilistic default: a claim is no surer than the weaker of "I trust this
  source this much" and "the source is this sure"; idempotent, so repeating a
  source adds nothing, and `combine w 1 = w`. The supplied source value stays
  a preserved record beside the holder's weight.

## The state found before this tracer

lean-nmms (main `acae35b`): the book's NMMS fully proved; nothing on weights.
Codex workspace branch `codex/uncertainty-provenance-prototype`: a proved
value-resolution operation (entry value, else source fallback, with
provenance), no inference. graph-nmms (main `17a29a1`): source-uncertainty
records preserved, no effective value computed, no entry weight.

## What is built

### lean-nmms, `LeanNmms/Possibilistic.lean` (namespace `NMMS.Possibilistic`)

`Scale`, `Q01`, `WEntry`/`WBase`, `cut`, `DerivableAt` (the book's
`Derivable` over `baseRel (cut B t)`, decidable by the existing instance),
`derivableAt` (`fastProve` over the cut), `degree?`, `DegreeGe`, `lift`,
`combine`. All proved, with the standard three axioms only
(`tests/AllConstantsAxioms.lean`: 2,243 constants):

| Theorem | Says |
|---|---|
| `derivable_mono`, `baseRel_mono`, `derivable_of_subset` | the calculus is monotone in the base (induction on `Derivable`) |
| `cut_zero`, `cut_antitone`, `cut_subset` | `B_0` is the whole base; the cut is antitone in `t` |
| `derivableAt_iff` | the procedure is correct at every threshold (`reasoner_correct`) |
| `derivableAt_antitone`, `derivableAt_zero_iff` | derivability is antitone in `t`; threshold 0 is the unweighted derivability |
| `cut_theorem` | degree ≥ `t` ⇔ `B_t` derives, for every `t` including 0 |
| `degree_none_iff`, `degree_sup`, `degree_sup_unique` | `none` ⇔ the whole base fails; the degree is the attained sup, unique up to the preorder |
| `degree_mono_base`, `decidableDegreeGe` | adding entries never lowers a degree; "degree ≥ t" is decidable |
| `weakest_link_lower`, `weakest_link_attained` | the degree is the max over deriving selections of their least weight |
| `lift_entries`, `cut_lift`, `derivableAt_lift`, `degree_lift` | all weights 1: every cut is the base; the degree is 1 for exactly the derivable sequents |
| `combine_le_holder`, `combine_le_source`, `combine_one`, `weight_bounds` | the min combination's bounds; weights lie in [0,1] |

Per-threshold `derivable_iff_valid` is the existing theorem applied to
`baseRel (cut B t)`, set-invariant by `baseRel_setInvariant`; no new
statement is needed.

`tests/PossibilisticExamples.lean` computes the shared example in the kernel
(`decide`) and by `#eval`: degree(p ⇒ q ∧ r) = 1/2, degree(p ⇒ q) = 1,
degree(r ⇒ s) = 0 while degree(q ⇒ p) = none, the empty base derives
nothing, the all-ones base agrees with plain NMMS, `combine 4/5 1/2 = 1/2`.

### lean-nmms, `nmms-lean` weighted queries (`Main.lean`)

Each entry may carry `"weight"`: a string `"n/d"` or `"n"` of digits (at most
40 each), the rational n/d in [0,1]; numbers are refused. `"threshold":
"n/d"` answers the usual fields over the cut and echoes the threshold;
`"degree": true` answers `{"id", "degree": "n/d" | null}`. A weighted query
needs a weight on every entry; weights without a weighted query, both
`threshold` and `degree`, weights above 1, denominator 0, and over-long
digit strings are refused. Unweighted queries are unchanged (graph-nmms's
existing 14 backend tests pass against the new binary).
`tests/test_possibilistic_cli.py`: 5 tests, pass.

### graph-nmms, `python/graph_nmms/possibilistic.py`

`WeightedBase(snapshot, weights, source_values=None)` with `.weight`,
`.source_value`, `.effective_weight`, `.candidates`; `cut`, `derivable_at`
(through the unchanged `LeanNmmsReasoner`; inconclusive is a `GraphError`),
`degree`, `combine_weight`, `weight` (the parser: Fraction, int, Decimal or
string; no default, no float). `tests/test_possibilistic.py`: 13 tests,
pass, including the real roles `pm-merge` entry weighted at thresholds 1/2
and 9/10.

### Differential test, Python `degree` against Lean `degree?`

Generated finite bases (1–4 entries, exact or monotone, weights in
{0, 1/4, 1/2, 3/4, 1}) and sequents with up to one connective per formula,
evaluated in Lean by `lake env lean` on the verified definition:
**200 of 200 agree for seed 20261031, and 200 of 200 for seed 7** (the two
runs took 106 s and 101 s). Default run: 40 cases.

## Next steps (not in this round)

1. Send weights through graph-nmms's `LeanNmmsReasoner` to the new
   `"degree"` query, so the differential test compares two independent
   paths (Python cut + plain query, versus Lean cut + degree) rather than
   the Python computation against the Lean definition.
2. Run the weighted merge-readiness case through the roles tracer's adapter
   at two thresholds (the plan's last condition; the entry is in the test).
3. Guarded entries in the generated bases of the differential test.

Side ideas go to the backlog, not here.

## Definition of done, and where it stands

- lean-nmms: `lake build` with 0 `sorry`; `tests/AllConstantsAxioms.lean`
  passes; `tests/PossibilisticExamples.lean` compiles with its `decide`
  examples; `tests/test_possibilistic_cli.py` passes. **Met.**
- graph-nmms: all 13 tests in `tests/test_possibilistic.py` pass, with the
  differential test agreeing with Lean on 200 generated bases for two seeds.
  **Met.**
- The plan's own conditions: the cut theorem and the weakest-link
  characterisation proved (**met**); graph-nmms stores entry weights
  (**met**, `WeightedBase`); one real merge-readiness case runs with weighted
  entries at two thresholds (**met in the test**; through the roles adapter:
  next step 2).
- Both branches merged to main after the sized security review. **Open**:
  the review's scope is the two parsers, `parseWeight` in `Main.lean` and
  `weight` in `possibilistic.py`; the proofs have no input surface.
- Effort used: 3 build rounds for the Lean proofs (17 of 17 on round 3; the
  resisting three were `simp` not finishing on `filter`/`map`, proved by
  induction or `List.filter_eq_self`), 1 round for the Python module, 1 for
  the command line.
