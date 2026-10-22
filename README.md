# lean-nmms

A Lean 4 formalization of the NMMS sequent calculus: machine-checked proofs, a
decision procedure, proof-certificate checkers, and a differential test against
the Python implementation pyNMMS.

## What NMMS is

NMMS is the nonmonotonic multi-succedent sequent calculus of Ulf Hlobil and
Robert Brandom (*Reasons for Logic, Logic for Reasons*, Routledge 2025,
chapter 3). It is a logic for logical expressivists: the logical vocabulary
(negation, conjunction, disjunction, implication) is added on top of a *base*
of material consequences between atomic sentences, such as "p, therefore q",
and makes explicit what the base already contains. A sequent `Γ ⇒ Δ` has a set
of sentences on each side, read as "it is out of order to accept everything in
Γ while rejecting everything in Δ". Sequents that share an atom hold
(Containment), and so do the sequents in the base. Because a base consequence
need not survive added premises, Weakening fails: `p ⇒ q` can hold while
`p, r ⇒ q` does not. Over the empty base the calculus derives exactly the
classically valid sequents, and over any base at least those.

## What pyNMMS is

[pyNMMS](https://github.com/bradleypallen/pyNMMS) (Bradley P. Allen, MIT
licence) is a Python reasoner for NMMS. A base entry is `EXACT` (any added
premise defeats it), `MONOTONE` (it survives any addition) or `GUARDED` (it
survives any addition except named defeaters). This project models pyNMMS
0.15.1's calculus and base semantics in Lean and compares the two on generated
cases.

## What is proved

Every theorem below is in namespace `NMMS`. Outside comments, no source file
contains `sorry`, `admit`, `native_decide`, `extern` or `axiom`; each of the
1,907 constants of `Main` and `LeanNmms` depends only on `propext`,
`Classical.choice` and `Quot.sound` (`tests/AllConstantsAxioms.lean`).
"Derivable" means derivable in the Lean definition `Derivable` (Calculus.lean).

- Sides are sets (order and repetition do not matter): `derivable_congr`
  (Calculus.lean), `derivable_congr_base`, `baseRel_setInvariant` (Base.lean).
- Containment extends to complex sentences: a sentence on both sides makes a
  sequent derivable, `overlap_derivable` (Containment.lean); the search's axiom
  test is sound, `axiomCheck_sound` (Decide.lean).
- The decision procedure `prove` is sound and complete, over every base:
  `proveN_sound`, `proveN_complete`, `prove_iff` (Decide.lean). It terminates
  with a depth bound equal to the connective count, `proveN_stable`
  (Decide.lean); `prove_iff` also gives `Derivable` a `Decidable` instance.
- Supraclassicality: every classically valid sequent is derivable over every
  base, `supraclassical`; over the empty base the derivable sequents are exactly
  the valid ones, `emptyBase_sound`, `emptyBase_iff_valid` (Classical.lean).
- Weakening fails: `weakening_fails`, with the instances `pq_exact_derives`,
  `pq_exact_not_weakened` and `pq_exact_not_weakened_neg` for the base
  `{p |~ q}`. `pq_monotone_weakened`: a `MONOTONE` entry keeps `p, r ⇒ q`.
  `pq_guarded`: a `GUARDED` entry with defeater `r` loses it when `r` is added
  and keeps it when another atom is added (Weakening.lean).
- Every rule is invertible over every set-invariant base: `invertibility`
  (statement `Invertibility` in Open.lean; proof in Invertibility.lean via
  `derivable_iff_valid`: a sequent is derivable exactly when every leaf of its
  complete decomposition is an axiom, with absorption lemma `C_uc`).
- A proof-tree certificate that `check` accepts is a derivation, over every
  base: `check_sound` (Certificate.lean). A one-branch "not derivable"
  certificate that `refute` accepts shows non-derivability over every
  set-invariant base, `refute_sound`; the non-backtracking search `fastProve`
  returns `true` exactly on derivable sequents, `fastProve_iff` (Refute.lean).
- Ordered derivations from initial premises: `Closure B Γ₀` is the set of
  sentences reachable from `Γ₀` by single-conclusion NMMS steps over base `B`.
  An accepted derivation puts the claim in it, `checkDerivation_sound`; an
  accepted closure refutation puts it outside and every atom it lists inside,
  `checkRefutation_sound`, via `valuation_sound` (every rule preserves truth
  under one valuation). All in Derivation.lean.
- Stratified defeasible closure over ground atoms: an accepted certificate's
  closure is exactly the defined closure and its applications exactly the
  applicable rules, `checkGroundClosure_exact`, `checkGroundClosure_sound`
  (Ground.lean); accepted entitlement rounds end at the least fixpoint,
  `checkEntitlement_sound` (Entitlement.lean).

## The decision procedure and `nmms-lean`

`NMMS.prove` mirrors pyNMMS's root-first search. `nmms-lean` reads JSON Lines
on standard input, answers with `NMMS.fastProve` (with `"engine":
"backtracking"`, `prove`) and writes one JSON line per query. A query has an
`id`, a `base` in pyNMMS's `MaterialBase.to_dict()` form, and `antecedent` and
`consequent` as lists of formula trees (not pyNMMS sentence strings):
`{"atom": "p"}`, `{"neg": F}`, `{"conj": [F, F]}`, `{"disj": [F, F]}`,
`{"impl": [F, F]}`. The header of `Main.lean` documents every field. Example
(`queries.jsonl`):

    {"id":"a","base":{"language":["p","q","r"],"consequences":[{"antecedent":["p"],"consequent":["q"],"robustness":{"kind":"exact"}}]},"antecedent":[{"atom":"p"}],"consequent":[{"atom":"q"}]}
    {"id":"b","base":{"language":["p","q","r"],"consequences":[{"antecedent":["p"],"consequent":["q"],"robustness":{"kind":"exact"}}]},"antecedent":[{"atom":"p"},{"atom":"r"}],"consequent":[{"atom":"q"}]}

    $ .lake/build/bin/nmms-lean < queries.jsonl
    {"cert_ok":null,"derivable":true,"id":"a","refute_len":null,"refute_ok":null}
    {"cert_ok":null,"derivable":false,"id":"b","refute_len":0,"refute_ok":true}

`p ⇒ q` holds over the base `{p |~ q}`; `p, r ⇒ q` does not. For an underivable
sequent the program also builds a one-branch refutation and checks it with the
proved `refute` (`refute_ok`, `refute_len`).

Two further request kinds, `"op": "closure"` and `"op": "score"`, check the
closure certificates and the ground and entitlement certificates above. Both
carry a `request_hash` (SHA-256 of the canonical JSON of the question) that the
checker recomputes and echoes. The `score` format was designed for a separate
Python library that is not part of this repository (see `LeanNmms/Score.lean`).

`--max-line-bytes` (default 4 MiB) and `--max-depth` (default 256 levels of
`{`/`[`) bound each input line; a line over either gets `{"error": ...}`.
There is no time limit inside the program and the procedure is exponential in
the worst case, so callers should enforce their own timeout.

## Certificates

A derivation certificate is a proof tree: `{"ax": true}` for an axiom leaf, or
`{"side": "L"|"R", "principal": F, "premises": [C]}` (three premises for
`L impl`, `L disj` and `R conj`). It carries only choices; the checker
recomputes every premise sequent itself, in one pass with no search. To check
one, add it to a query as `cert`:

    {"id":"c","base":{"language":["p","q"],"consequences":[]},"antecedent":[{"conj":[{"atom":"p"},{"atom":"q"}]}],"consequent":[{"atom":"q"}],"cert":{"side":"L","principal":{"conj":[{"atom":"p"},{"atom":"q"}]},"premises":[{"ax":true}]}}

The answer has `"cert_ok": true`; a wrong certificate gets `false`.

Trusted when a certificate is accepted: `check_sound` (checked by the Lean
kernel), the compiled checker (Lean's compiler, not the kernel) and the JSON
reading in `Main.lean`. To remove the compiler from the trusted part, state the
certificate as a Lean term and let the kernel evaluate `check R c Γ Δ = true`
by `decide`, as `LeanNmms/Weakening.lean` does for decisions.

## Differential test

`difftest/difftest.py` compares `nmms-lean` with pyNMMS 0.15.1 (pinned, with
the wheel's hash, in `difftest/requirements.txt`). Each case builds a base over
atoms p, q, r, s (0 to 4 entries, mixing EXACT, MONOTONE and GUARDED) through
pyNMMS's API, and a sequent of random formulas, sent to Lean with sides
shuffled and duplicated. It checks that: both give the same verdict (pyNMMS
with a fresh reasoner and with a shared persistent cache); pyNMMS's parse equals
the generated tree; every derivable case's certificate, rebuilt from pyNMMS's
trace, is accepted; every Lean "not derivable" has an accepted refutation; and
an invertibility probe agrees (for each complex sentence, the conclusion is
derivable exactly when the rule's premises are).

Recorded results (`difftest/summary-*.json`); both runs have 0 disagreements, 0
cache disagreements, 0 parser mismatches and 0 Lean errors:

| Summary file | Seed, depth, width | Cases | Derivable | Certificates accepted | Refutations accepted | Invertibility failures | Lean timeouts |
|---|---|---|---|---|---|---|---|
| `summary-main-fast.json` | 20261012, 3, 3 | 5,000 | 2,280 | 2,280 of 2,280 | 2,720 of 2,720 | 0 of 7,377 | 0 |
| `summary-deep-fast.json` | 7, 4, 4 | 2,000 | 1,151 | 1,151 of 1,151 | 849 of 849 | 0 of 4,180 | 0 |

`summary-main.json` and `summary-deep.json` are earlier runs of the same cases
with the backtracking engine: 0 disagreements, and 5 Lean timeouts at 10 s in
the deep run (`disagreements-deep.jsonl`); re-run with a 15-minute limit
(`rerun-timeouts.txt`), 3 finished and agree with pyNMMS and 2 did not. Not
covered: pyNMMS's sentence parser (trees are sent), `max_depth`, ontology and
RDF bases, atom names beyond plain identifiers.

## Build and test

The toolchain is pinned in `lean-toolchain` (Lean 4.34.1). There are no
dependencies (no Mathlib). Install [elan](https://github.com/leanprover/elan),
then:

    lake build                                    # library and .lake/build/bin/nmms-lean
    lake env lean Axioms.lean                     # prints the axioms each main theorem uses
    lake env lean tests/AllConstantsAxioms.lean   # prints FIXES_AXIOMS_OK 1907 constants
    lake env lean tests/FixesDerivation.lean      # kernel examples (also FixesGround.lean)
    python3 -I difftest/malformed_test.py         # 9 input-hardening checks

Differential test (see "Differential test"): `python3 -m venv VENV`, then
`VENV/bin/pip install --only-binary :all: --require-hashes -r difftest/requirements.txt`,
then `VENV/bin/python -I difftest/difftest.py --cases 500`.

`.github/workflows/ci.yml` runs these on every push and pull request.
`tests/test_fixes_lean.py` (run with `python3 -m unittest -v tests.test_fixes_lean`) runs
the kernel examples, the JSON entry point, a source scan and the axiom audit.

## Known limits and open questions

- `Derivable` is checked against pyNMMS by differential testing and against the
  book by reading its main text (not the appendix proofs); faithfulness to
  either is tested, not proved. Recorded differences: Containment is built into
  the atomic axioms, as in pyNMMS; pyNMMS's shortcuts on non-atomic sequents
  are proved admissible rather than taken as axioms; the principal sentence is
  always removed from the premise context, as pyNMMS does (the book's rules
  allow it to stay; that the two coincide follows from invertibility but is not
  stated as a theorem). Kaplan's two-premise system is not covered.
- `Closure` is monotone: a step may use any subset of what is reached, so a
  `GUARDED` entry's defeater among the initial premises does not block a step
  whose premises leave it out. pyNMMS's whole-set rounds can reach fewer atoms
  and are not modelled; a round-based closure in Lean is an open extension.
- The closure-refutation check is conservative, not complete (an exclusion
  entry or a several-consequent entry firing on the reached set makes it refuse).
- `findRefute` is not proved to find a refutation for every underivable
  sequent (each one it returns is checked by `refute`). Not attempted: failure
  of Cut; equality of pyNMMS's memo cache with no cache (tested only).
- Unverified code: `Main.lean`, the request binding (`LeanNmms/Wire.lean`,
  tested against Python's `hashlib` and `json`), and the score checker's
  grounding, guard evaluation, attribution and projection. That
  `GroundClosure` and the entitlement fixpoint match the external library is
  tested against that library's logs, not proved.
- We found no earlier mechanization of NMMS (Lean, Rocq, Isabelle, Agda); the
  search was web-based and not exhaustive.

## Credits

NMMS is due to Ulf Hlobil and Robert B. Brandom, *Reasons for Logic, Logic for
Reasons: Pragmatics, Semantics, and Conceptual Roles* (Routledge, 2025). The
reference implementation and the base-robustness policies are Bradley P.
Allen's [pyNMMS](https://github.com/bradleypallen/pyNMMS) (MIT). Pairing a Lean model with
differential testing of the production code follows "How We Built Cedar"
(FSE 2024). Developed by Taylor-Made Labs with AI coding assistance (Claude).

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT), at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this work, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
