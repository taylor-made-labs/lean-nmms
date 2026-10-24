/-
  LeanNmms.Open

  Statements written as `Prop` definitions (not as theorems with `sorry`), so
  that the library stays free of `sorry`. `NMMS.Invertibility` is proved:
  `NMMS.invertibility` in `LeanNmms/Invertibility.lean`.

  Invertibility of every rule (the book's Prop. 27, as reported), stated in
  the book's form: for any context `Γ` (which may itself contain the
  principal sentence), the conclusion `Γ, φ ⇒ Δ` (or `Γ ⇒ Δ, φ`) is derivable
  exactly when every premise of φ's rule is. The `←` directions are the rules
  themselves; the `→` directions are invertibility proper.

  Two consequences matter for the implementation:
  * the decision procedures may decompose any one complex sentence, with the
    principal sentence removed from its side, and never backtrack over that
    choice; the book's other rule instances (context keeping the principal
    sentence) derive nothing more;
  * a "not derivable" certificate can be one failing branch (a path of rule
    applications ending in an atomic sequent that is not in the base),
    linear in size.
-/
import LeanNmms.Calculus

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- Every rule is invertible over every set-invariant base. -/
def Invertibility (α : Type) [DecidableEq α] : Prop :=
  ∀ (R : BaseRel α), R.SetInvariant → ∀ (Γ Δ : List (Formula α)) (A B : Formula α),
    (Derivable R (neg A :: Γ) Δ ↔ Derivable R Γ (A :: Δ)) ∧
    (Derivable R (impl A B :: Γ) Δ ↔
      Derivable R Γ (A :: Δ) ∧ Derivable R (B :: Γ) Δ ∧ Derivable R (B :: Γ) (A :: Δ)) ∧
    (Derivable R (conj A B :: Γ) Δ ↔ Derivable R (A :: B :: Γ) Δ) ∧
    (Derivable R (disj A B :: Γ) Δ ↔
      Derivable R (A :: Γ) Δ ∧ Derivable R (B :: Γ) Δ ∧ Derivable R (A :: B :: Γ) Δ) ∧
    (Derivable R Γ (neg A :: Δ) ↔ Derivable R (A :: Γ) Δ) ∧
    (Derivable R Γ (impl A B :: Δ) ↔ Derivable R (A :: Γ) (B :: Δ)) ∧
    (Derivable R Γ (conj A B :: Δ) ↔
      Derivable R Γ (A :: Δ) ∧ Derivable R Γ (B :: Δ) ∧ Derivable R Γ (A :: B :: Δ)) ∧
    (Derivable R Γ (disj A B :: Δ) ↔ Derivable R Γ (A :: B :: Δ))

end NMMS
