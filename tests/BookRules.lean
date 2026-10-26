import Lean
import LeanNmms.Decide

/- Independent transcription of the finite NMMS rules in Hlobil and Brandom,
   RLLR chapter 3, printed pp108–111, corroborated by Brandom's May2025
   lectures p40. See docs/nmms-source-correspondence.md for sources and scope.

   Keep this reference separate from the implementation: review changes to
   its constructors against the sources, not merely against Derivable.
   It shares the library's formula syntax and finite-set representation, but
   does not define derivability through a decision procedure or leaf semantics.
   Its contexts are unrestricted and its sole axiom uses the supplied base.
   Every correspondence theorem below keeps that same base unchanged. -/
namespace BookRulesTests

open NMMS Formula
variable {α : Type} [DecidableEq α]

/-- The source's eight rules and atomic axiom, with explicit set congruence
    for the list representation of finite contexts. -/
inductive BookDerivable (R : BaseRel α) : List (Formula α) → List (Formula α) → Prop where
  | ax {Γ Δ} : allAtomic Γ = true → allAtomic Δ = true →
      R (atomsOf Γ) (atomsOf Δ) = true → BookDerivable R Γ Δ
  | congr {Γ Δ Γ' Δ'} : BookDerivable R Γ Δ → SetEq Γ Γ' → SetEq Δ Δ' →
      BookDerivable R Γ' Δ'
  | negL {Γ Δ A} : BookDerivable R Γ (A :: Δ) → BookDerivable R (neg A :: Γ) Δ
  | implL {Γ Δ A B} : BookDerivable R Γ (A :: Δ) → BookDerivable R (B :: Γ) Δ →
      BookDerivable R (B :: Γ) (A :: Δ) → BookDerivable R (impl A B :: Γ) Δ
  | conjL {Γ Δ A B} : BookDerivable R (A :: B :: Γ) Δ → BookDerivable R (conj A B :: Γ) Δ
  | disjL {Γ Δ A B} : BookDerivable R (A :: Γ) Δ → BookDerivable R (B :: Γ) Δ →
      BookDerivable R (A :: B :: Γ) Δ → BookDerivable R (disj A B :: Γ) Δ
  | negR {Γ Δ A} : BookDerivable R (A :: Γ) Δ → BookDerivable R Γ (neg A :: Δ)
  | implR {Γ Δ A B} : BookDerivable R (A :: Γ) (B :: Δ) → BookDerivable R Γ (impl A B :: Δ)
  | conjR {Γ Δ A B} : BookDerivable R Γ (A :: Δ) → BookDerivable R Γ (B :: Δ) →
      BookDerivable R Γ (A :: B :: Δ) → BookDerivable R Γ (conj A B :: Δ)
  | disjR {Γ Δ A B} : BookDerivable R Γ (A :: B :: Δ) → BookDerivable R Γ (disj A B :: Δ)

variable {R : BaseRel α} {Γ Δ : List (Formula α)}

theorem book_to_lean (hS : R.SetInvariant) (h : BookDerivable R Γ Δ) : Derivable R Γ Δ := by
  induction h with
  | ax hg hd hb => exact Derivable.ax hg hd hb
  | congr _ e1 e2 ih => exact derivable_congr hS ih e1 e2
  | negL _ ih => exact Derivable.negL SetEq.rfl' ih
  | implL _ _ _ ih1 ih2 ih3 => exact Derivable.implL SetEq.rfl' ih1 ih2 ih3
  | conjL _ ih => exact Derivable.conjL SetEq.rfl' ih
  | disjL _ _ _ ih1 ih2 ih3 => exact Derivable.disjL SetEq.rfl' ih1 ih2 ih3
  | negR _ ih => exact Derivable.negR SetEq.rfl' ih
  | implR _ ih => exact Derivable.implR SetEq.rfl' ih
  | conjR _ _ _ ih1 ih2 ih3 => exact Derivable.conjR SetEq.rfl' ih1 ih2 ih3
  | disjR _ ih => exact Derivable.disjR SetEq.rfl' ih

omit [DecidableEq α] in
theorem lean_to_book (h : Derivable R Γ Δ) : BookDerivable R Γ Δ := by
  induction h with
  | ax hg hd hb => exact BookDerivable.ax hg hd hb
  | negL e _ ih => exact BookDerivable.congr (BookDerivable.negL ih) e.symm SetEq.rfl'
  | implL e _ _ _ ih1 ih2 ih3 =>
    exact BookDerivable.congr (BookDerivable.implL ih1 ih2 ih3) e.symm SetEq.rfl'
  | conjL e _ ih => exact BookDerivable.congr (BookDerivable.conjL ih) e.symm SetEq.rfl'
  | disjL e _ _ _ ih1 ih2 ih3 =>
    exact BookDerivable.congr (BookDerivable.disjL ih1 ih2 ih3) e.symm SetEq.rfl'
  | negR e _ ih => exact BookDerivable.congr (BookDerivable.negR ih) SetEq.rfl' e.symm
  | implR e _ ih => exact BookDerivable.congr (BookDerivable.implR ih) SetEq.rfl' e.symm
  | conjR e _ _ _ ih1 ih2 ih3 =>
    exact BookDerivable.congr (BookDerivable.conjR ih1 ih2 ih3) SetEq.rfl' e.symm
  | disjR e _ ih => exact BookDerivable.congr (BookDerivable.disjR ih) SetEq.rfl' e.symm

/-- Same supplied base on both sides; no Containment hypothesis. -/
theorem book_iff_lean (hS : R.SetInvariant) :
    BookDerivable R Γ Δ ↔ Derivable R Γ Δ := ⟨book_to_lean hS, lean_to_book⟩

theorem fastProve_iff_book (hS : R.SetInvariant) :
    fastProve R Γ Δ = true ↔ BookDerivable R Γ Δ :=
  (fastProve_iff hS Γ Δ).trans (book_iff_lean hS).symm

theorem prove_iff_book (hS : R.SetInvariant) :
    prove R Γ Δ = true ↔ BookDerivable R Γ Δ :=
  (prove_iff hS Γ Δ).trans (book_iff_lean hS).symm

/-- Both production searches implement the reference over exactly baseRel B. -/
theorem concrete_reasoners_iff_book (B : List (Entry α)) (Γ Δ : List (Formula α)) :
    (fastProve (baseRel B) Γ Δ = true ↔ BookDerivable (baseRel B) Γ Δ) ∧
    (prove (baseRel B) Γ Δ = true ↔ BookDerivable (baseRel B) Γ Δ) :=
  ⟨fastProve_iff_book (baseRel_setInvariant B), prove_iff_book (baseRel_setInvariant B)⟩

end BookRulesTests

open Lean Elab Command

-- Enforce the dependency boundary; printing axioms alone would not fail CI.
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`BookRulesTests).isPrefixOf name then
      checked := checked + 1
      for ax in ← collectAxioms name do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "disallowed axiom {ax} in reference declaration {name}"
  if checked == 0 then throwError "no reference declarations audited"
  logInfo m!"BOOK_RULES_AXIOMS_OK {checked} declarations"
