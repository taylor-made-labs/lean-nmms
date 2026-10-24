# NMMS source correspondence

[`tests/BookRules.lean`](../tests/BookRules.lean) keeps a separate transcription of the published rule schemas and proves that the library derives exactly the same sequents over the **same supplied base**. Neither side adds Containment, and the equivalence does not assume it.

## Sources

The transcription was checked against these author-hosted primary sources:

| Source | Relevant pages | SHA-256 of inspected PDF |
|---|---|---|
| Hlobil and Brandom, [*Reasons for Logic, Logic for Reasons*, chapter 3](https://sites.pitt.edu/~rbrandom/Courses/2024%20Philosophy%20of%20Language/Texts/RLLR%20Chapter%203.pdf) | Printed pp108–111: base, axiom, rules, sets; pp150–153: proof search, conservativity, invertibility | `4b5e9307ca59013407c49820a39380cea73afc6fa2f42e0d9e9a3a45735d30ad` |
| Brandom, [*Vocabularies of Reason*, May2025 Pufendorf lectures](https://sites.pitt.edu/~rbrandom/Texts/Vocabularies%20of%20Reason%2025-5-23%20b.pdf) | p40: all eight rules and the distinction between arbitrary bases and containment bases | `a0957b7681295931fcb26dd80798d04d3165820a17e5187702bd196b67d9b079` |

The rule diagrams were visually inspected. The chapter comes from the author's 2024 course; its bytes have not been authenticated against the publisher's final edition. The May2025 lectures describe the recently published book and independently corroborate the same eight schemas. These hashes identify the reviewed copies if the hosted files change. Source comparison last checked: 2026-10-24.

## Rule mapping

The reference constructor and production constructor have the same name under `BookRulesTests.BookDerivable` and `NMMS.Derivable`, respectively:

| Constructor | Source clause | Premise structure checked |
|---|---|---|
| `ax` | Atomic axiom | Both sides atomic; the supplied base contains the sequent |
| `negL` | L¬ | Operand on the right |
| `negR` | R¬ | Operand on the left |
| `conjL` | L∧ | Both operands on the left |
| `conjR` | R∧ | Three premises: each operand separately, then both, on the right |
| `disjL` | L∨ | Three premises: each operand separately, then both, on the left |
| `disjR` | R∨ | Both operands on the right |
| `implL` | L→ | Three premises: antecedent right, consequent left, then both placements |
| `implR` | R→ | Antecedent left and consequent right |

All premises share their context. A context may contain the principal formula. The reference's additional `congr` constructor expresses equality of finite sets represented by lists; it does not add weakening or Cut. Production instead places set-equality evidence on rule conclusions and proves `NMMS.derivable_congr`.

## What the check establishes

`book_to_lean` and `lean_to_book` use constructor induction to establish `book_iff_lean`. They do not use search results or decomposition semantics to define the reference. The only base hypothesis is `R.SetInvariant`: order and repetition in the list representation do not change atomic membership.

`fastProve_iff_book` and `prove_iff_book` then connect both actual search functions to the reference. `concrete_reasoners_iff_book` specializes this to every entry list `B`, using `baseRel_setInvariant`; it needs no caller-supplied assumption. Every result keeps `R`, or `baseRel B`, unchanged.

Run after building the library:

```sh
lake env lean tests/BookRules.lean
```

The file also fails if a reference declaration depends on any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. Success reports `BOOK_RULES_AXIOMS_OK` with the audited declaration count.

## Trust boundary and maintenance

People must check that the transcription represents the source. Lean verifies the resulting mathematical correspondence; it does not read or authenticate the PDFs. The reference shares the library's formula syntax, atomic-membership helpers, and finite-set representation, so it is not an independent implementation of those components or the JSON parser.

The scope is finite propositional sequents with decidable atomic membership. The comparison makes no claim about separate closure/score operations, infinite sequents, or later modal extensions. Review reference-constructor changes against the primary sources rather than adjusting them solely to make a production change pass.
