/-
  LeanNmms.Calculus

  The NMMS sequent calculus over a material base, as pyNMMS 0.15.1 implements
  it (`pynmms/reasoner.py`) and as Hlobil and Brandom (2025, ch. 3) state it.

  * The base is any Boolean relation `R` on lists of atom names (read as sets).
    pyNMMS's concrete base semantics is in `LeanNmms.Base`.
  * Axioms are *atomic* sequents that either share an atom (Containment, which
    pyNMMS always adds, `MaterialBase.is_axiom` "Ax1") or are in the base.
    pyNMMS's extra shortcuts for non-atomic sequents are not axioms here; they
    are proved admissible in `LeanNmms.Containment`.
  * The eight rules carry the third top sequents of the book and of pyNMMS.
    The principal formula is removed from its side in every premise
    (`rest`), exactly like pyNMMS's `without_left` / `without_right`.
-/
import LeanNmms.Syntax

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- A material base, abstractly: which atomic sequents (as atom-name lists) it
contains. Containment is supplied by the calculus, not by `R`. -/
abbrev BaseRel (α : Type) := List α → List α → Bool

/-- The two sides share a sentence. -/
def Overlap (Γ Δ : List (Formula α)) : Prop := ∃ φ, φ ∈ Γ ∧ φ ∈ Δ

/-- Derivability in NMMS over base `R`: `Derivable R Γ Δ` is `Γ ⇒ Δ`. -/
inductive Derivable (R : BaseRel α) : List (Formula α) → List (Formula α) → Prop where
  /-- Axiom: an atomic sequent that obeys Containment or is in the base. -/
  | ax {Γ Δ} : allAtomic Γ = true → allAtomic Δ = true →
      ((∃ a, atom a ∈ Γ ∧ atom a ∈ Δ) ∨ R (atomsOf Γ) (atomsOf Δ) = true) →
      Derivable R Γ Δ
  /-- [L¬] Γ, ¬A ⇒ Δ  ⇐  Γ ⇒ Δ, A -/
  | negL {Γ Δ A} : neg A ∈ Γ →
      Derivable R (rest Γ (neg A)) (A :: Δ) → Derivable R Γ Δ
  /-- [L→] Γ, A→B ⇒ Δ  ⇐  Γ ⇒ Δ, A;  Γ, B ⇒ Δ;  Γ, B ⇒ Δ, A -/
  | implL {Γ Δ A B} : impl A B ∈ Γ →
      Derivable R (rest Γ (impl A B)) (A :: Δ) →
      Derivable R (B :: rest Γ (impl A B)) Δ →
      Derivable R (B :: rest Γ (impl A B)) (A :: Δ) → Derivable R Γ Δ
  /-- [L∧] Γ, A∧B ⇒ Δ  ⇐  Γ, A, B ⇒ Δ -/
  | conjL {Γ Δ A B} : conj A B ∈ Γ →
      Derivable R (A :: B :: rest Γ (conj A B)) Δ → Derivable R Γ Δ
  /-- [L∨] Γ, A∨B ⇒ Δ  ⇐  Γ, A ⇒ Δ;  Γ, B ⇒ Δ;  Γ, A, B ⇒ Δ -/
  | disjL {Γ Δ A B} : disj A B ∈ Γ →
      Derivable R (A :: rest Γ (disj A B)) Δ →
      Derivable R (B :: rest Γ (disj A B)) Δ →
      Derivable R (A :: B :: rest Γ (disj A B)) Δ → Derivable R Γ Δ
  /-- [R¬] Γ ⇒ Δ, ¬A  ⇐  Γ, A ⇒ Δ -/
  | negR {Γ Δ A} : neg A ∈ Δ →
      Derivable R (A :: Γ) (rest Δ (neg A)) → Derivable R Γ Δ
  /-- [R→] Γ ⇒ Δ, A→B  ⇐  Γ, A ⇒ Δ, B -/
  | implR {Γ Δ A B} : impl A B ∈ Δ →
      Derivable R (A :: Γ) (B :: rest Δ (impl A B)) → Derivable R Γ Δ
  /-- [R∧] Γ ⇒ Δ, A∧B  ⇐  Γ ⇒ Δ, A;  Γ ⇒ Δ, B;  Γ ⇒ Δ, A, B -/
  | conjR {Γ Δ A B} : conj A B ∈ Δ →
      Derivable R Γ (A :: rest Δ (conj A B)) →
      Derivable R Γ (B :: rest Δ (conj A B)) →
      Derivable R Γ (A :: B :: rest Δ (conj A B)) → Derivable R Γ Δ
  /-- [R∨] Γ ⇒ Δ, A∨B  ⇐  Γ ⇒ Δ, A, B -/
  | disjR {Γ Δ A B} : disj A B ∈ Δ →
      Derivable R Γ (A :: B :: rest Δ (disj A B)) → Derivable R Γ Δ

/-- Two lists with the same members. -/
def SetEq {β : Type} (l l' : List β) : Prop := ∀ x, x ∈ l ↔ x ∈ l'

theorem SetEq.cons {β : Type} {l l' : List β} (x : β) (h : SetEq l l') :
    SetEq (x :: l) (x :: l') := by
  intro y; simp [h y]

theorem SetEq.rest {l l' : List (Formula α)} (φ : Formula α) (h : SetEq l l') :
    SetEq (NMMS.rest l φ) (NMMS.rest l' φ) := by
  intro y; simp [h y]

theorem SetEq.atomsOf {l l' : List (Formula α)} (h : SetEq l l') :
    SetEq (NMMS.atomsOf l) (NMMS.atomsOf l') := by
  intro y; simp [h (atom y)]

/-- A base relation that only looks at which atoms are on each side. -/
def BaseRel.SetInvariant (R : BaseRel α) : Prop :=
  ∀ a b a' b', SetEq a a' → SetEq b b' → R a b = R a' b'

/-- **Sides are sets.** Derivability depends only on the members of each side,
provided the base does. This is what licenses modelling pyNMMS's `frozenset`
sides by lists. -/
theorem derivable_congr {R : BaseRel α} (hR : R.SetInvariant)
    {Γ Δ : List (Formula α)} (h : Derivable R Γ Δ) :
    ∀ {Γ' Δ'}, SetEq Γ Γ' → SetEq Δ Δ' → Derivable R Γ' Δ' := by
  induction h with
  | ax hg hd hor =>
    intro Γ' Δ' e1 e2
    refine Derivable.ax ?_ ?_ ?_
    · rw [allAtomic_iff] at *; intro φ hφ; exact hg φ ((e1 φ).mpr hφ)
    · rw [allAtomic_iff] at *; intro φ hφ; exact hd φ ((e2 φ).mpr hφ)
    · rcases hor with ⟨a, h1, h2⟩ | hb
      · exact Or.inl ⟨a, (e1 _).mp h1, (e2 _).mp h2⟩
      · right; rw [← hR _ _ _ _ e1.atomsOf e2.atomsOf]; exact hb
  | negL hm _ ih =>
    intro Γ' Δ' e1 e2
    exact Derivable.negL ((e1 _).mp hm) (ih (e1.rest _) (e2.cons _))
  | implL hm _ _ _ ih1 ih2 ih3 =>
    intro Γ' Δ' e1 e2
    exact Derivable.implL ((e1 _).mp hm) (ih1 (e1.rest _) (e2.cons _))
      (ih2 ((e1.rest _).cons _) e2) (ih3 ((e1.rest _).cons _) (e2.cons _))
  | conjL hm _ ih =>
    intro Γ' Δ' e1 e2
    exact Derivable.conjL ((e1 _).mp hm) (ih (((e1.rest _).cons _).cons _) e2)
  | disjL hm _ _ _ ih1 ih2 ih3 =>
    intro Γ' Δ' e1 e2
    exact Derivable.disjL ((e1 _).mp hm) (ih1 ((e1.rest _).cons _) e2)
      (ih2 ((e1.rest _).cons _) e2) (ih3 (((e1.rest _).cons _).cons _) e2)
  | negR hm _ ih =>
    intro Γ' Δ' e1 e2
    exact Derivable.negR ((e2 _).mp hm) (ih (e1.cons _) (e2.rest _))
  | implR hm _ ih =>
    intro Γ' Δ' e1 e2
    exact Derivable.implR ((e2 _).mp hm) (ih (e1.cons _) ((e2.rest _).cons _))
  | conjR hm _ _ _ ih1 ih2 ih3 =>
    intro Γ' Δ' e1 e2
    exact Derivable.conjR ((e2 _).mp hm) (ih1 e1 ((e2.rest _).cons _))
      (ih2 e1 ((e2.rest _).cons _)) (ih3 e1 (((e2.rest _).cons _).cons _))
  | disjR hm _ ih =>
    intro Γ' Δ' e1 e2
    exact Derivable.disjR ((e2 _).mp hm) (ih e1 (((e2.rest _).cons _).cons _))

end NMMS
