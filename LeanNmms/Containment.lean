/-
  LeanNmms.Containment

  1. A reusable induction principle, `derivable_of_preserved`: if a property of
     sequents is kept by the premises of every rule, and implies derivability on
     atomic sequents, it implies derivability everywhere. It is proved by
     induction on the total connective count, so it also shows that full
     decomposition always ends (the measure falls on every premise).
  2. Containment for every sentence (Reflexivity in the book's terms):
     `Γ ⇒ Δ` is derivable whenever the sides share any sentence, atomic or
     complex. pyNMMS uses both as axiom shortcuts on non-atomic sequents
     (`NMMSReasoner._is_axiom`); these lemmas show the shortcuts are admissible.
-/
import LeanNmms.Calculus

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- The termination measure: total connective count of both sides. -/
def measure (Γ Δ : List (Formula α)) : Nat := weight Γ + weight Δ

theorem exists_complex {l : List (Formula α)} (h : ¬ allAtomic l = true) :
    ∃ φ ∈ l, φ.isAtom = false := by
  simp [allAtomic] at h
  obtain ⟨φ, h1, h2⟩ := h
  exact ⟨φ, h1, by simpa using h2⟩

/-- Closes the measure side conditions: a premise is lighter than its conclusion. -/
macro "meas" : tactic =>
  `(tactic| (simp only [measure, weight_cons, Formula.conn] at *; omega))

/-- **Decomposition principle.** If `P` holds of a sequent, is inherited by the
premises of every rule applicable to it, and gives derivability on atomic
sequents, then the sequent is derivable. -/
theorem derivable_of_preserved (R : BaseRel α)
    (P : List (Formula α) → List (Formula α) → Prop)
    (hax : ∀ Γ Δ, allAtomic Γ = true → allAtomic Δ = true → P Γ Δ → Derivable R Γ Δ)
    (hnegL : ∀ Γ Δ A, neg A ∈ Γ → P Γ Δ → P (rest Γ (neg A)) (A :: Δ))
    (himplL : ∀ Γ Δ A B, impl A B ∈ Γ → P Γ Δ →
      P (rest Γ (impl A B)) (A :: Δ) ∧ P (B :: rest Γ (impl A B)) Δ ∧
      P (B :: rest Γ (impl A B)) (A :: Δ))
    (hconjL : ∀ Γ Δ A B, conj A B ∈ Γ → P Γ Δ → P (A :: B :: rest Γ (conj A B)) Δ)
    (hdisjL : ∀ Γ Δ A B, disj A B ∈ Γ → P Γ Δ →
      P (A :: rest Γ (disj A B)) Δ ∧ P (B :: rest Γ (disj A B)) Δ ∧
      P (A :: B :: rest Γ (disj A B)) Δ)
    (hnegR : ∀ Γ Δ A, neg A ∈ Δ → P Γ Δ → P (A :: Γ) (rest Δ (neg A)))
    (himplR : ∀ Γ Δ A B, impl A B ∈ Δ → P Γ Δ → P (A :: Γ) (B :: rest Δ (impl A B)))
    (hconjR : ∀ Γ Δ A B, conj A B ∈ Δ → P Γ Δ →
      P Γ (A :: rest Δ (conj A B)) ∧ P Γ (B :: rest Δ (conj A B)) ∧
      P Γ (A :: B :: rest Δ (conj A B)))
    (hdisjR : ∀ Γ Δ A B, disj A B ∈ Δ → P Γ Δ → P Γ (A :: B :: rest Δ (disj A B))) :
    ∀ n Γ Δ, measure Γ Δ < n → P Γ Δ → Derivable R Γ Δ := by
  intro n
  induction n with
  | zero => intro Γ Δ h; omega
  | succ n ih =>
    intro Γ Δ hm hP
    by_cases hg : allAtomic Γ = true
    · by_cases hd : allAtomic Δ = true
      · exact hax Γ Δ hg hd hP
      · obtain ⟨φ, hφ, hna⟩ := exists_complex hd
        have hw := weight_rest hφ
        cases φ with
        | atom a => simp [isAtom] at hna
        | neg A =>
          exact Derivable.negR hφ (ih _ _ (by meas) (hnegR _ _ _ hφ hP))
        | impl A B =>
          exact Derivable.implR hφ (ih _ _ (by meas) (himplR _ _ _ _ hφ hP))
        | conj A B =>
          obtain ⟨h1, h2, h3⟩ := hconjR _ _ _ _ hφ hP
          exact Derivable.conjR hφ (ih _ _ (by meas) h1) (ih _ _ (by meas) h2)
            (ih _ _ (by meas) h3)
        | disj A B =>
          exact Derivable.disjR hφ (ih _ _ (by meas) (hdisjR _ _ _ _ hφ hP))
    · obtain ⟨φ, hφ, hna⟩ := exists_complex hg
      have hw := weight_rest hφ
      cases φ with
      | atom a => simp [isAtom] at hna
      | neg A =>
        exact Derivable.negL hφ (ih _ _ (by meas) (hnegL _ _ _ hφ hP))
      | impl A B =>
        obtain ⟨h1, h2, h3⟩ := himplL _ _ _ _ hφ hP
        exact Derivable.implL hφ (ih _ _ (by meas) h1) (ih _ _ (by meas) h2)
          (ih _ _ (by meas) h3)
      | conj A B =>
        exact Derivable.conjL hφ (ih _ _ (by meas) (hconjL _ _ _ _ hφ hP))
      | disj A B =>
        obtain ⟨h1, h2, h3⟩ := hdisjL _ _ _ _ hφ hP
        exact Derivable.disjL hφ (ih _ _ (by meas) h1) (ih _ _ (by meas) h2)
          (ih _ _ (by meas) h3)

/-- Shared atom ⇒ derivable, whatever else is on the sides. -/
theorem atom_overlap (R : BaseRel α) {a : α} {Γ Δ : List (Formula α)}
    (h1 : atom a ∈ Γ) (h2 : atom a ∈ Δ) : Derivable R Γ Δ := by
  refine derivable_of_preserved R (fun Γ Δ => atom a ∈ Γ ∧ atom a ∈ Δ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (measure Γ Δ + 1) Γ Δ (by omega) ⟨h1, h2⟩
  · intro Γ Δ _ _ ⟨h1, h2⟩; exact Derivable.ax ‹_› ‹_› (Or.inl ⟨a, h1, h2⟩)
  all_goals (intros; simp_all)

/-- **Containment for all sentences**: shared sentence ⇒ derivable. -/
theorem overlap_derivable (R : BaseRel α) :
    ∀ (φ : Formula α) {Γ Δ : List (Formula α)}, φ ∈ Γ → φ ∈ Δ → Derivable R Γ Δ := by
  intro φ
  induction φ with
  | atom a => intro Γ Δ h1 h2; exact atom_overlap R h1 h2
  | neg A ih =>
    intro Γ Δ h1 h2
    refine Derivable.negL h1 (Derivable.negR (A := A) (by simp [h2]) ?_)
    exact ih (by simp) (by simp [ne_neg A])
  | conj A B ihA ihB =>
    intro Γ Δ h1 h2
    refine Derivable.conjL h1 (Derivable.conjR h2 ?_ ?_ ?_)
    · exact ihA (by simp) (by simp)
    · exact ihB (by simp) (by simp)
    · exact ihA (by simp) (by simp)
  | disj A B ihA ihB =>
    intro Γ Δ h1 h2
    refine Derivable.disjL h1 (Derivable.disjR h2 ?_) (Derivable.disjR h2 ?_)
      (Derivable.disjR h2 ?_)
    · exact ihA (by simp) (by simp)
    · exact ihB (by simp) (by simp)
    · exact ihA (by simp) (by simp)
  | impl A B ihA ihB =>
    intro Γ Δ h1 h2
    refine Derivable.implL h1 (Derivable.implR (A := A) (B := B) (by simp [h2]) ?_)
      (Derivable.implR h2 ?_) (Derivable.implR (A := A) (B := B) (by simp [h2]) ?_)
    · exact ihA (by simp) (by simp [ne_impl_l A B])
    · exact ihB (by simp) (by simp)
    · exact ihB (by simp) (by simp)

end NMMS
