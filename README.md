# lean-nmms

> **Redesign, 2 Nov 2026, 13:30 Eastern.** This README describes `lean-nmms` as it should be after the suite's re-architecture (the direction paper, `DIRECTION.md`, in the suite's private repository). **The code in this repo does not match it yet.** Bring the code into line with this README, not the README into line with the code. The README that described the code as built is kept at [`docs/README-as-built-2026-11-02.md`](docs/README-as-built-2026-11-02.md).

## What it is

The Lean-verified reasoner underneath graph-nmms: a Lean 4 formalization of the NMMS sequent calculus, with machine-checked proofs, a decision procedure and proof-certificate checkers.

**Zone:** reasoning core. Purple: the commitments cluster.

## How it fits

- **Takes in:** sequents over a base of material consequences, from graph-nmms.
- **Gives out:** a proved verdict, or a certificate that can be re-checked, to graph-nmms, and through it to every commitments product.
- **Rule:** it is the bottom of the stack. Learned weights and trained deciders never reach it; they rank and route, and the logic decides.

## What it absorbs or becomes

Nothing is absorbed. It keeps its job; the redesign changes who calls it, not what it proves.

## Gap from today's code

These are the alignment work items, drawn from the README that described the code as built.

- The proofs and the differential test against pyNMMS need no change for the redesign.
- Score certificates were produced by ntaild; their producer moves to graph-nmms and process-commitments, and this repo keeps checking them.
- Callers pin a checker build by its hash. Keep the pinning story simple and documented as more products call it.
- Check that the interface graph-nmms needs for edge relations and inhibitions is covered, and add to it only if a real gap shows up.

## Links

- The suite's direction paper (`DIRECTION.md`) and its product map are in the suite's private repository.
- [README as built, before the redesign](docs/README-as-built-2026-11-02.md)
