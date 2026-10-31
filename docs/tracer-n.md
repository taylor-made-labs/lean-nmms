# Tracer N: possibilistic weights in lean-nmms and graph-nmms

Status: tests and statements first (31 Oct 2026). Nothing here is proved or
built yet beyond what this page says. Branch `tests/tracer-n` in both
repositories; never merged with a `sorry` or a failing test.

## Direction (Taylor, 30 Oct)

- Uncertainty is a first-class citizen: weights inside one agent's model,
  plus each source's own uncertainty value.
- Possibilistic logic is the foundation.
- The threshold `t` can be 0.
- Lean covers the core computation at every threshold, not only the
  "true" fragment.
- The work is not held back for publish-ready research.

The plan (`records/plans/turn-13-suite-alignment/map.md`, tracer N) adds: the
cut theorem (degree = the largest `t` at which `B_t` derives, the weakest-link
rule), and `derivable_iff_valid` holding per threshold.

## The state found

**lean-nmms** (main `acae35b`, public as taylor-made-labs/lean-nmms): the
book's NMMS, fully proved, no `sorry`: `Derivable` is the calculus;
`reasoner_correct` says the decision procedures `fastProve` and `prove` accept
exactly the derivable sequents over any pyNMMS base `baseRel B`;
`derivable_iff_valid` and `invertibility` give the leaf characterisation; a
`Decidable` instance exists for every finite base. **Nothing about weights,
degrees or thresholds exists.** (`weight` in `Syntax.lean` is the connective
count, a different thing; the graded theory uses `WEntry.weight`.) No
lemma says derivability is monotone in the base; it is needed and small.

**Codex workspace** (`~/dev/suite-workspace-for-gpt`, branch
`codex/uncertainty-provenance-prototype`, one commit `a55f029`): a proved
*value-resolution* operation (use the entry's own value when present, else the
source's configured fallback, with provenance kept). It imports no NMMS module
and states nothing about inference, cuts or degrees. Its charter
(`planning/uncertainty-research-charter.md`) left the meaning of a value (U18)
and the mathematical effect (U20) open; Taylor's 30 Oct direction settles
both: possibilistic weights, cut semantics. The charter's demands that still
bind this tracer: a name apart from the book's NMMS (here
`NMMS.Possibilistic`), nothing attributed to the book, every claim stated
independently of the implementation, counterexamples kept.

**graph-nmms** (main `17a29a1`, pins lean-nmms `acae35b`): stores source
uncertainty as preserved records (`uncertainty_coverage`,
`resolve_uncertainty`, claim `uncertainty` carriers) and explicitly computes
no effective value. Its `LeanNmmsReasoner` sends a whole snapshot to
`nmms-lean` and returns `derivable` / `not_derivable` / `inconclusive`.
**No entry weight, no cut, no degree exists.**

**hetzner** has the pinned toolchain (`~/.elan`, Lean 4.34.1) and a built
`nmms-lean` from the roles tracer; the build cache was reused, so the new
module builds in under a second.

## What this round delivers

### lean-nmms: `LeanNmms/Possibilistic.lean` (statements, 17 `sorry`)

Design (reasons in the file header):

- A scale `Scale W`: a decidable total preorder with `zero` and `one`.
  Possibilistic logic is ordinal, so only the order is used. `Q01`, the
  rationals in `[0,1]`, is the executable instance (its transitivity is
  proved; it is on the computational path).
- `WEntry` = a pyNMMS `Entry` with its holder's weight; `WBase` is a list.
- `cut B t` = the entries weighted `t` or more; `cut B zero` is the whole
  base, so a weight-0 entry takes part at threshold 0 and nowhere else.
- `DerivableAt B t Γ Δ` = the book's `Derivable` over `baseRel (cut B t)`;
  decidable by the existing instance; `derivableAt` is `fastProve` over the
  cut and `derivableAt_iff` is `reasoner_correct` (proved, no new idea).
- `degree? B Γ Δ : Option W` = the largest candidate threshold (`zero` or an
  entry's weight) at which the cut derives the sequent; `none` when no cut
  does. The `Option` is forced by the cut theorem at `t = 0`: with a degree
  in `[0,1]`, "degree ≥ 0" would always hold, but `B_0 ⊢` does not.
- `combine holder source = min` for a source's own uncertainty.

Statements to prove (all `sorry`), and what each follows from:

| Theorem | Says | Follows from |
|---|---|---|
| `derivable_mono` | derivability is monotone in the base relation | new: induction on `Derivable` |
| `baseRel_mono` | more entries, larger relation | new: `List.any` over a superset |
| `cut_zero` | `B_0` is the whole base | new: filter with `zero_le` |
| `cut_antitone`, `cut_subset` | monotonicity of the cut in `t` | new: filter with `le_trans` |
| `derivableAt_antitone` | derivable at `t` ⇒ at every `s ≤ t` | the three above (term given) |
| `derivableAt_zero_iff` | threshold 0 is the unweighted derivability | `cut_zero` (proved) |
| `cut_theorem` | degree ≥ `t` ⇔ `B_t` derives, every `t`, 0 included | the one real argument: the least weight in `cut B t` is a candidate ≥ `t` whose cut contains `cut B t` |
| `degree_none_iff` | `none` ⇔ not even the whole base derives | `cut_theorem` at `zero` |
| `degree_sup`, `degree_sup_unique` | the degree is the sup and is attained; unique up to the preorder | `cut_theorem` |
| `degree_mono_base` | adding entries never lowers a degree | `cut_theorem`, `derivable_mono` |
| `decidableDegreeGe` | "degree ≥ t" decidable for finite bases | `cut_theorem` (instance given) |
| `weakest_link_lower` | a deriving selection's least weight bounds the degree below | `cut_theorem`, `derivable_mono` |
| `weakest_link_attained` | the degree is the least weight of some deriving selection (`cut B d`) | `cut_theorem` |
| `lift_entries`, `cut_lift` | all-ones base: every cut is the whole base | `le_one` |
| `derivableAt_lift` | at every `t`, agreement with the book's derivability | `cut_lift` (proved) |
| `degree_lift` | degree is `one` for the derivable sequents, `none` otherwise | `cut_lift`, `reasoner_correct` |
| `combine_le_holder`, `combine_le_source` | min is below both | case split on `le_total` |
| `weight_bounds`, `combine_one`, `derivable_nil`, `derivableAt_iff`, `Q01.le_trans` | proved now | — |

Per-threshold `derivable_iff_valid` needs no new statement: it is the
existing theorem applied to `baseRel (cut B t)`, which is set-invariant by
`baseRel_setInvariant`.

`tests/PossibilisticExamples.lean` computes the shared example by `decide`
(kernel) and `#eval`: degree(p ⇒ q ∧ r) = 1/2, degree(p ⇒ q) = 1,
degree(r ⇒ s) = 0 while degree(q ⇒ p) = none, the empty base derives
nothing, the all-ones base agrees with plain NMMS, and `combine 4/5 1/2 =
1/2`. All nine outputs match.

On this branch `tests/AllConstantsAxioms.lean` and CI's `sorry` scan fail by
design.

### graph-nmms: `tests/test_possibilistic.py` (13 tests, 12 failing)

They specify `graph_nmms.possibilistic`: `WeightedBase(snapshot, weights,
source_values=None)` with `.weight`, `.source_value`, `.effective_weight`;
`cut(weighted, t)`; `derivable_at(weighted, t, ant, con, reasoner)`;
`degree(weighted, ant, con, reasoner) -> Fraction | None`;
`combine_weight(holder, source) -> min`. Cases: degree at 0, a middle value
and 1; the cut theorem on the example; ties and the strongest alternative
support; the empty base; a source's value combined by min and preserved; the
real roles `pm-merge` entry weighted, at thresholds 1/2 and 9/10; and the
differential test against Lean's `degree?` on generated finite bases
(`TRACER_N_CASES`, default 40; `TRACER_N_SEED`).

Every failing test's first assertion names the missing piece. The Lean oracle
of the differential test (`lean_degrees`, through `lake env lean`) runs
today; `LeanOracleWorksToday` passes, so the differential test fails only for
the stated reason.

Why min for the combination: possibilistic logic's conjunction is min, and a
claim is no surer than the weaker of "I trust this source this much" and
"the source is this sure". It is ordinal (no calibration needed), idempotent
(repeating a source adds nothing, as the charter requires), and `combine w 1
= w`. The source's supplied value stays a preserved record next to the
holder's weight; only the effective weight changes.

## Plan

1. Prove the 17 statements in the order of the table (the small lemmas
   first; `cut_theorem` is the one with content; the rest are corollaries).
   Limit: three rounds per proof, then it is reported as a conjecture
   (plan's limit).
2. Build `graph_nmms/possibilistic.py` against the tests. Weights are
   `Fraction`; strings and ints are accepted and converted exactly; floats
   are refused (as the snapshot format already refuses them).
3. Extend `nmms-lean` with an optional `"weights"` and `"threshold"` /
   `"degree"` query, so graph-nmms can ask Lean directly instead of filtering
   in Python (the differential test then compares two independent paths).
4. Run the weighted merge-readiness case through the roles tracer's adapter
   at two thresholds.

Side ideas go to the backlog, not here.

## Definition of done

- lean-nmms: `lake build` with 0 `sorry` in `LeanNmms/Possibilistic.lean`;
  `tests/AllConstantsAxioms.lean` passes again (every constant depends only
  on `propext`, `Classical.choice`, `Quot.sound`); `tests/PossibilisticExamples.lean`
  compiles with its `decide` examples.
- graph-nmms: all 13 tests in `tests/test_possibilistic.py` pass (the 12
  specification tests and the oracle check), with the differential test
  agreeing with Lean on 200 generated bases (`TRACER_N_CASES=200`) for two
  seeds.
- The plan's own conditions: the cut theorem and the weakest-link
  characterisation proved; graph-nmms stores entry weights; one real
  merge-readiness case runs with weighted entries at two thresholds.
- Both branches merged to main after the sized security review (the Lean
  side has no input surface; the Python side parses weights, so that parser
  is the review's scope).
- Effort limit: three proof rounds per theorem, and two build rounds for the
  Python module, before what remains is reported as open.
