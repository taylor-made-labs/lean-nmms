# lean-nmms

A Lean 4 formalization of the NMMS sequent calculus: machine-checked proofs, a
decision procedure that accepts exactly the sequents NMMS derives from the
supplied base, proof-certificate checkers, and a differential test against
the Python implementation pyNMMS.

## What NMMS is

NMMS is the nonmonotonic multi-succedent sequent calculus of Ulf Hlobil and
Robert Brandom (*Reasons for Logic, Logic for Reasons*, Routledge 2025,
chapter 3, pp. 108–111). It is a logic for logical expressivists: the logical
vocabulary (negation, conjunction, disjunction, implication) is added on top
of a *base* of material consequences between atomic sentences, such as "p,
therefore q", and makes explicit what the base already contains. A sequent
`Γ ⇒ Δ` has a set of sentences on each side, read as "it is out of order to
accept everything in Γ while rejecting everything in Δ".

The axioms are exactly the atomic sequents in the base, and nothing else.
In particular Containment (a sentence on both sides) is not an axiom unless
the base contains it: over a base without `p |~ p`, `p ⇒ p` is not
derivable, and over the empty base nothing is derivable at all. The eight
rules (L/R for ¬, ∧, ∨, →) add no structural rules; L→, L∨ and R∧ each have a
third premise that combines the other two. Because a base consequence need
not survive added premises, Weakening fails: `p ⇒ q` can hold while
`p, r ⇒ q` does not. Over a base that obeys Containment every classically
valid sequent is derivable; over the base whose only consequences are the
Containment instances, exactly the classically valid ones are.

## What pyNMMS is

[pyNMMS](https://github.com/bradleypallen/pyNMMS) (Bradley P. Allen, MIT
licence) is a Python reasoner for NMMS. A base entry is `EXACT` (any added
premise defeats it), `MONOTONE` (it survives any addition) or `GUARDED` (it
survives any addition except named defeaters). This project reads pyNMMS
0.15.1's base format and compares the two on generated cases. pyNMMS differs
from NMMS over the supplied base in one known way: its axiom test also
accepts every sequent whose sides share an atom or a complex sentence, i.e.
it adds Containment to the base. Its verdict over a base B is therefore NMMS
derivability over B plus Containment, not over B (see "Differential test").

## What is proved

Every theorem below is in namespace `NMMS`. Outside comments and string
literals, no source file
contains `sorry`, `admit`, `native_decide`, `extern` or `axiom`; each of the
2,052 constants of `Main` and `LeanNmms` depends only on `propext`,
`Classical.choice` and `Quot.sound` (`tests/AllConstantsAxioms.lean`).
"Derivable" means derivable in the Lean definition `Derivable`
(Calculus.lean), which is the specification: the chapter's axiom clause and
eight rules, with sides read as sets. In the book `Γ, A` is `Γ ∪ {A}`, so a
rule's context may itself contain the principal sentence; `Derivable` allows
that (each rule takes its context explicitly). Nothing else is built in.

- The axioms are the base, exactly: an atomic sequent is derivable if and
  only if it is in the supplied base, `derivable_atomic_iff`. Over the empty
  base nothing is derivable, `emptyBase_underivable` (Calculus.lean).
- Sides are sets (order and repetition do not matter): `derivable_congr`
  (Calculus.lean), `derivable_congr_base`, `baseRel_setInvariant` (Base.lean).
- **The reasoner is correct.** Over every set-invariant base, the default
  search `fastProve` and the backtracking search `prove` return `true`
  exactly on the derivable sequents: `fastProve_iff`, `prove_iff`; for the
  pyNMMS bases that `nmms-lean` reads, with no hypothesis,
  `reasoner_correct` (Decide.lean). Both take their axioms from the base
  alone (`axiomCheck`, no Containment or other shortcut). Search depth is
  bounded by the connective count, `proveN_stable`. Derivability over a
  pyNMMS base has a `Decidable` instance, evaluated by the kernel in the
  `decide` examples.
- Every rule is invertible over every set-invariant base, in the book's form
  (any context, the principal sentence possibly in it): `invertibility`
  (statement `Invertibility` in Open.lean; proof in Invertibility.lean via
  `derivable_iff_valid`: a sequent is derivable exactly when every leaf of
  its complete decomposition is in the base, with absorption lemma `C_uc` and
  `S_congr`). So the book's rule instances whose context keeps the principal
  sentence derive nothing more than those that remove it,
  `negL_keep_iff` for L¬.
- Certificates. A proof-tree certificate that `check` accepts is a
  derivation, over every base, `check_sound`; every derivable sequent has
  one, `check_complete`; together `certifiable_iff` (Certificate.lean). A
  one-branch "not derivable" certificate that `refute` accepts shows
  non-derivability, `refute_sound`; every underivable sequent has one,
  `refute_complete`, `refutable_iff`; an accepted one is no longer than the
  connective count, `refute_length`. `findRefute`, which `nmms-lean` runs,
  returns only refutations that `refute` accepts, `findRefute_sound`, and
  returns one on every underivable sequent, `findRefute_complete`; so the
  program's `"refute_ok"` is `true` exactly on the underivable sequents,
  `refuteOk_iff` (Refute.lean).
- Containment and classical logic, as theorems about bases that supply
  Containment, never as defaults. In two forms: `BaseRel.Containment` (every
  atom of the atom type) and `BaseRel.ContainmentOn L` (the atoms of a
  language `L`). The MONOTONE entries `a |~ a`, one per `a ∈ L`
  (`coEntries L`), give any base the second, `containmentOn_coEntries`
  (Base.lean); over `String` or `Nat` atoms they never give the first. Over
  a base with `ContainmentOn L`, a sentence over `L` on both sides makes a
  sequent derivable, `overlap_derivable_on` (Containment.lean), and every
  classically valid sequent over `L` is derivable, `supraclassical_on`; for
  the base `B ++ coEntries L` these are `overlap_derivable_coEntries` and
  `supraclassical_coEntries`. The global forms are `overlap_derivable` and
  `supraclassical`. Every derivable sequent is classically valid when every
  base sequent is, `classical_sound`; over the base of all Containment
  instances the derivable sequents are exactly the valid ones,
  `containmentBase_iff_valid` (Classical.lean).
- Weakening fails: `weakening_fails`, with the instances `pq_exact_derives`,
  `pq_exact_not_weakened` and `pq_exact_not_weakened_neg` for the base
  `{p |~ q}`. `pq_monotone_weakened`: a `MONOTONE` entry keeps `p, r ⇒ q`.
  `pq_guarded`: a `GUARDED` entry with defeater `r` loses it when `r` is added
  and keeps it when another atom is added. `empty_base_no_identity`,
  `excluded_middle_not_derived`, `excluded_middle_with_rr`: no Containment
  is added (Weakening.lean).
- Ordered derivations from initial premises (a further calculation, not NMMS
  derivability: NMMS has no Cut, and `Closure` also contains its initial
  premises and lets a step use any subset of what has been reached):
  `Closure B Γ₀` is the set of sentences reachable from `Γ₀` by chained
  single-conclusion NMMS steps over base `B`.
  An accepted derivation puts the claim in it, `checkDerivation_sound`; an
  accepted closure refutation puts it outside and every atom it lists inside,
  `checkRefutation_sound`, via `valuation_sound` (every rule preserves truth
  under one valuation; Classical.lean). The rest is in Derivation.lean.
  `nmms-lean` reports this as
  `"in_closure"`, never as `"derivable"`.
- Stratified defeasible closure over ground atoms: an accepted certificate's
  closure is exactly the defined closure and its applications exactly the
  applicable rules, `checkGroundClosure_exact`, `checkGroundClosure_sound`
  (Ground.lean); accepted entitlement rounds end at the least fixpoint,
  `checkEntitlement_sound` (Entitlement.lean). These are separate
  calculations, not NMMS derivability.

## The decision procedure and `nmms-lean`

`nmms-lean` reads JSON Lines on standard input, answers with
`NMMS.fastProve` (with `"engine": "backtracking"`, `NMMS.prove`, which tries
every choice of principal sentence as pyNMMS does) and writes one JSON line
per query. `"derivable"` is NMMS derivability from the supplied base and
nothing else. A query has an `id`, a `base` in pyNMMS's
`MaterialBase.to_dict()` form, and `antecedent` and `consequent` as lists of
formula trees (not pyNMMS sentence strings): `{"atom": "p"}`, `{"neg": F}`,
`{"conj": [F, F]}`, `{"disj": [F, F]}`, `{"impl": [F, F]}`. The header of
`Main.lean` documents every field of the sequent and closure queries (the
`score` request is described in `LeanNmms/Score.lean`). Example
(`queries.jsonl`):

    {"id":"a","base":{"language":["p","q","r"],"consequences":[{"antecedent":["p"],"consequent":["q"],"robustness":{"kind":"exact"}}]},"antecedent":[{"atom":"p"}],"consequent":[{"atom":"q"}]}
    {"id":"b","base":{"language":["p","q","r"],"consequences":[{"antecedent":["p"],"consequent":["q"],"robustness":{"kind":"exact"}}]},"antecedent":[{"atom":"p"},{"atom":"r"}],"consequent":[{"atom":"q"}]}
    {"id":"c","base":{"language":["p"],"consequences":[]},"antecedent":[{"atom":"p"}],"consequent":[{"atom":"p"}]}

    $ .lake/build/bin/nmms-lean < queries.jsonl
    {"cert_ok":null,"derivable":true,"id":"a","refute_len":null,"refute_ok":null}
    {"cert_ok":null,"derivable":false,"id":"b","refute_len":0,"refute_ok":true}
    {"cert_ok":null,"derivable":false,"id":"c","refute_len":0,"refute_ok":true}

`p ⇒ q` holds over the base `{p |~ q}`; `p, r ⇒ q` does not; and `p ⇒ p`
does not hold over the empty base. To have Containment, put it in the base:
a `MONOTONE` entry `a |~ a` for each atom `a`. For an underivable sequent the
program also builds a one-branch refutation and checks it with the proved
`refute` (`refute_ok`, `refute_len`).

The base's `language`, when given, must contain every atom of the base and
of the query (the base is a relation on sets of atoms of that language); a
query with another atom gets `{"error": ...}` rather than an answer. Without
`language`, the atoms that occur are the language. A base that lists the
same pair twice is refused (pyNMMS keeps one policy per pair), and so is a
robustness value pyNMMS refuses: defeaters (`unless`) on an EXACT or
MONOTONE entry, or an exclusion pair with no atoms; defeater atoms must be
in the `language` too. A formula object must have exactly one key, and a
certificate node must be `{"ax": true}` or a rule node on a complex
sentence with `"side"` `"L"` or `"R"`. Two inputs that the JSON reader would
silently reinterpret are refused: a line with an unpaired UTF-16 surrogate
escape (such as a lone `\udc80`), which it would turn into U+FFFD so that
distinct names become one, and an object that repeats a key, of which it
would keep only the last value. In each case the program answers about the
base and sequent as written or not at all. Errors found before the line is
parsed (bad JSON or UTF-8, a line too long or nested too deeply, a
surrogate, a repeated key) carry no `id`; blank lines get no answer.

Two further request kinds, `"op": "closure"` and `"op": "score"`, check the
closure certificates and the ground and entitlement certificates above. Both
carry a `request_hash` (SHA-256 of the canonical JSON of the question) that the
checker recomputes and echoes. The closure answer's verdict field is
`"in_closure"`. The `score` format was designed for a separate Python library
that is not part of this repository (see `LeanNmms/Score.lean`).

`--max-line-bytes` (default 4 MiB) and `--max-depth` (default 256 levels of
`{`/`[`) bound each input line; a line over either gets `{"error": ...}`.
There is no time limit inside the program. The default search costs the size
of one complete decomposition tree (exponential in the number of
three-premise rules in the worst case); the backtracking search can also be
exponential in the number of choices on underivable sequents, so callers
should enforce their own timeout.

## Certificates

A derivation certificate is a proof tree: `{"ax": true}` for an axiom leaf
(an atomic sequent in the base), or `{"side": "L"|"R", "principal": F,
"keep": bool, "premises": [C]}` (three premises for `L impl`, `L disj` and
`R conj`; `keep` is optional, default `false`, and `true` selects the book's
instance whose context keeps the principal sentence). It carries only
choices; the checker recomputes every premise sequent itself, in one pass
with no search. To check one, add it to a query as `cert`:

    {"id":"c","base":{"language":["p","q"],"consequences":[{"antecedent":["p","q"],"consequent":["q"]}]},"antecedent":[{"conj":[{"atom":"p"},{"atom":"q"}]}],"consequent":[{"atom":"q"}],"cert":{"side":"L","principal":{"conj":[{"atom":"p"},{"atom":"q"}]},"premises":[{"ax":true}]}}

The answer has `"cert_ok": true`; a wrong certificate gets `false` (over the
empty base this one gets `false`, since its leaf `p, q ⇒ q` is not in it).

Trusted when a certificate is accepted: `check_sound` (checked by the Lean
kernel), the compiled checker (Lean's compiler, not the kernel) and the JSON
reading in `Main.lean`. To remove the compiler from the trusted part, state the
certificate as a Lean term and let the kernel evaluate `check R c Γ Δ = true`
by `decide`, as `tests/NmmsRules.lean` does.

## Differential test

`difftest/difftest.py` compares `nmms-lean` with pyNMMS 0.15.1 (pinned, with
the wheel's hash, in `difftest/requirements.txt`). The harness builds a base B
over atoms p, q, r, s (0 to 4 entries, mixing EXACT, MONOTONE and GUARDED)
through pyNMMS's API, shared by `--per-base` (default 3) consecutive cases;
each case is a sequent of random formulas, sent to Lean with sides
shuffled and duplicated. Since pyNMMS adds Containment, it checks that:
pyNMMS over B (with a fresh reasoner and with a shared persistent cache)
gives the same verdict as Lean over B plus Containment (a MONOTONE `a |~ a`
for each atom); pyNMMS's parse equals the generated tree; every derivable
case's certificate, rebuilt from pyNMMS's trace, is accepted over B plus
Containment (a non-atomic leaf that pyNMMS accepted by its shared-sentence
shortcut is expanded into its full decomposition, which Lean checks leaf by
leaf); Lean over B itself agrees with `difftest/nmms_reference.py`, a small
stdlib implementation of the chapter's rules; every Lean "not derivable" has
an accepted refutation; and two invertibility probes agree (for each complex
sentence, the conclusion is derivable exactly when all of its rule's
premises are): one on pyNMMS, i.e. over B plus Containment, and one on
`nmms-lean` over B itself (the theorem `invertibility` proves the latter).
`containment_changed` counts the cases where pyNMMS's added Containment
changes the verdict.

Recorded results (`difftest/summary-*.json`); both runs have 0 disagreements
with pyNMMS (over B plus Containment), 0 disagreements with the reference
(over B), 0 cache disagreements, 0 parser mismatches and 0 Lean errors:

| Summary file | Seed, depth, width | Cases | Derivable over B+CO (pyNMMS, `pynmms_derivable`) | NMMS-derivable over B (`nmms_derivable`) | Containment changed the verdict | Certificates accepted | Refutations accepted | Invertibility failures, pyNMMS (B+CO) | Invertibility failures, NMMS (B) | Lean timeouts |
|---|---|---|---|---|---|---|---|---|---|---|
| `summary-main-fast.json` | 20261012, 3, 3 | 5,000 | 2,280 | 723 | 1,557 | 2,280 of 2,280 | 6,997 of 6,997 | 0 of 7,377 | 0 of 7,377 | 0 |
| `summary-deep-fast.json` | 7, 4, 4 | 2,000 | 1,151 | 263 | 888 | 1,151 of 1,151 | 2,586 of 2,586 | 0 of 4,180 | 0 of 4,180 | 0 |

The deep run was made with `--timeout 60`; its slowest Lean answer (checking
an expanded pyNMMS certificate) took 20.4 s. `difftest/rerun_timeouts.py`
replays the queries of a recorded timeout (the same base, the certificate
rebuilt from pyNMMS's trace, the same `--max-line-bytes`) in a fresh
`nmms-lean` with a longer time limit. Not covered: pyNMMS's sentence
parser (trees are sent), `max_depth`, ontology and RDF bases, atom names
beyond plain identifiers.

## Build and test

The toolchain is pinned in `lean-toolchain` (Lean 4.34.1). There are no
dependencies (no Mathlib). Install [elan](https://github.com/leanprover/elan),
then:

    lake build                                    # library and .lake/build/bin/nmms-lean
    lake env lean Axioms.lean                     # prints the axioms each main theorem uses
    lake env lean tests/AllConstantsAxioms.lean   # prints FIXES_AXIOMS_OK 2052 constants
    lake env lean tests/NmmsRules.lean            # kernel examples of the chapter's rules
    lake env lean tests/FixesDerivation.lean      # kernel examples (also FixesGround.lean)
    python3 -I difftest/malformed_test.py         # 37 input-hardening checks
    python3 -B -m unittest -v tests.test_nmms_rules   # rules vs. the stdlib reference

Differential test (see "Differential test"): `python3 -m venv VENV`, then
`VENV/bin/pip install --only-binary :all: --require-hashes -r difftest/requirements.txt`,
then `VENV/bin/python -I difftest/difftest.py --cases 500`.

`.github/workflows/ci.yml` runs these on every push and pull request.
`tests/test_fixes_lean.py` (run with `python3 -m unittest -v tests.test_fixes_lean`) runs
the kernel examples, the JSON entry point, a source scan and the axiom audit.

## Known limits and open questions

- `Derivable` is checked against the chapter by reading its rules (pp.
  108–111), against an independent Python transcription of them by testing,
  and against pyNMMS (plus Containment) by differential testing; faithfulness
  to the printed rules is a matter of reading, not proof. Kaplan's
  two-premise system is not covered.
- NMMS takes its axioms from the base as supplied. pyNMMS's documentation
  describes the chapter's material bases as obeying Containment; this
  library neither adds nor requires that, and a base that should obey it
  must say so (MONOTONE `a |~ a` entries, `coEntries`). The theorems that
  need it take it as a hypothesis (`ContainmentOn L` for sequents over `L`).
- `EXACT`/`MONOTONE`/`GUARDED` are pyNMMS's way of describing which atomic
  sequents are in the base; `baseRel` (Base.lean) fixes that reading, and
  NMMS uses the resulting set of atomic sequents as its axioms. The
  `language`, duplicate-pair, robustness, surrogate and strict-parsing checks
  are in the unverified JSON shell; the shell refuses a few robustness values
  that pyNMMS reads leniently (listed in the `Main.lean` header).
- `Closure` is monotone: a step may use any subset of what is reached, so a
  `GUARDED` entry's defeater among the initial premises does not block a step
  whose premises leave it out. pyNMMS's whole-set rounds can reach fewer atoms
  and are not modelled; a round-based closure in Lean is an open extension.
- The closure-refutation check is conservative, not complete (an exclusion
  entry or a several-consequent entry firing on the reached set makes it refuse).
- Not attempted: failure of Cut as a theorem; equality of pyNMMS's memo cache
  with no cache (tested only); a memoizing search.
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
