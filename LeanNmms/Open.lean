/-
  LeanNmms.Open

  Statements written as `Prop` definitions (not as theorems with `sorry`), so
  that the library stays free of `sorry`. `NMMS.Invertibility` is now proved:
  `NMMS.invertibility` in `LeanNmms/Invertibility.lean`,
  by the "cleaner route" named at the end of this header. The original notes
  follow.

  Invertibility of every rule (the book's Prop. 27, as reported) for the
  calculus as pyNMMS implements it: sides read as sets, the principal sentence
  removed from its side in the premises. It matters for two things:
  * a short certificate for "not derivable": with invertibility, one failing
    branch (a path of rule applications ending in an atomic non-axiom) is a
    refutation, linear in size; without it, a refutation must cover every
    choice of principal sentence at every node;
  * a fast decision procedure: with invertibility the search can decompose
    any one complex sentence and never backtrack over the choice.

  Evidence so far: the differential harness's invertibility probe compares,
  for every complex sentence of every generated sequent, the conclusion's
  derivability with that of all its premises (by pyNMMS, which agrees with the
  verified Lean procedure on every case run); see README, "Differential test".

  Obstacle (not attempted beyond analysis). Induction on the derivation of
  `Γ ⇒ Δ`, permuting the rule on `φ` above the last rule on `ψ ≠ φ`, needs
  an absorption lemma whenever `φ` is also produced by `ψ`'s rule as a
  subformula (for example `φ = ¬A`, `ψ = ¬A ∧ B`): the inverted premise lacks
  `φ` while the rebuilt `ψ` premise contains it again. With set sides this
  closes by applying `φ`'s own rule once more (`X ⇒ A, Δ` gives
  `¬A, X ⇒ A, Δ` by L¬ and set idempotence), but the lemma has to be stated
  and proved for every pair of rules; a cleaner route may be to characterize
  derivability by the leaves of complete decompositions and show those leaves
  do not depend on the order.
-/
import LeanNmms.Calculus

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- The open goal: every rule is invertible over every set-invariant base. -/
def Invertibility (α : Type) [DecidableEq α] : Prop :=
  ∀ (R : BaseRel α), R.SetInvariant → ∀ (Γ Δ : List (Formula α)), Derivable R Γ Δ →
    (∀ A, neg A ∈ Γ → Derivable R (rest Γ (neg A)) (A :: Δ)) ∧
    (∀ A B, impl A B ∈ Γ →
      Derivable R (rest Γ (impl A B)) (A :: Δ) ∧
      Derivable R (B :: rest Γ (impl A B)) Δ ∧
      Derivable R (B :: rest Γ (impl A B)) (A :: Δ)) ∧
    (∀ A B, conj A B ∈ Γ → Derivable R (A :: B :: rest Γ (conj A B)) Δ) ∧
    (∀ A B, disj A B ∈ Γ →
      Derivable R (A :: rest Γ (disj A B)) Δ ∧
      Derivable R (B :: rest Γ (disj A B)) Δ ∧
      Derivable R (A :: B :: rest Γ (disj A B)) Δ) ∧
    (∀ A, neg A ∈ Δ → Derivable R (A :: Γ) (rest Δ (neg A))) ∧
    (∀ A B, impl A B ∈ Δ → Derivable R (A :: Γ) (B :: rest Δ (impl A B))) ∧
    (∀ A B, conj A B ∈ Δ →
      Derivable R Γ (A :: rest Δ (conj A B)) ∧
      Derivable R Γ (B :: rest Δ (conj A B)) ∧
      Derivable R Γ (A :: B :: rest Δ (conj A B))) ∧
    (∀ A B, disj A B ∈ Δ → Derivable R Γ (A :: B :: rest Δ (disj A B)))

end NMMS
