/-
  LeanNmms.Classical

  Supraclassicality (Hlobil and Brandom 2025, ch. 3, Fact 2) and the
  characterization of the empty base (Appendix Prop. 25, as reported from the
  main text): NMMS over any base derives every classically valid sequent, and
  over the empty base (Containment only, which pyNMMS always adds) it derives
  exactly the classically valid sequents.

  Classical validity is the multi-succedent reading: every Boolean valuation
  that makes all of `Γ` true makes some member of `Δ` true.

  Proof idea. Supraclassicality uses the decomposition principle
  `derivable_of_preserved` with "classically valid" as the preserved property:
  each rule's premises are valid when its conclusion is (the third premises
  included), and a valid atomic sequent must share an atom. The empty-base
  direction is induction on derivations: each rule is classically sound.
-/
import LeanNmms.Containment

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- Classical truth of a formula under a valuation of the atoms. -/
def Formula.eval (v : α → Bool) : Formula α → Bool
  | atom a => v a
  | neg A => !A.eval v
  | conj A B => A.eval v && B.eval v
  | disj A B => A.eval v || B.eval v
  | impl A B => !A.eval v || B.eval v

/-- Multi-succedent classical validity of `Γ ⇒ Δ`. -/
def Valid (Γ Δ : List (Formula α)) : Prop :=
  ∀ v : α → Bool, (∀ φ ∈ Γ, φ.eval v = true) → ∃ ψ ∈ Δ, ψ.eval v = true

/-- If everything but `φ` is true, and `φ` is true, everything is true. -/
theorem all_of_rest {v : α → Bool} {Γ : List (Formula α)} {φ : Formula α}
    (h1 : ∀ x ∈ rest Γ φ, x.eval v = true) (h2 : φ.eval v = true) :
    ∀ x ∈ Γ, x.eval v = true := by
  intro x hx
  by_cases h : x = φ
  · subst h; exact h2
  · exact h1 x (by simp [hx, h])

/-- A true member of `Δ` is either `φ` or a true member of `rest Δ φ`. -/
theorem pick {v : α → Bool} {Δ : List (Formula α)} (φ : Formula α)
    (h : ∃ ψ ∈ Δ, ψ.eval v = true) :
    φ.eval v = true ∨ ∃ ψ ∈ rest Δ φ, ψ.eval v = true := by
  obtain ⟨ψ, hψ, hv⟩ := h
  by_cases e : ψ = φ
  · subst e; exact Or.inl hv
  · exact Or.inr ⟨ψ, by simp [hψ, e], hv⟩

theorem ex_cons {v : α → Bool} {Δ : List (Formula α)} (A : Formula α)
    (h : ∃ ψ ∈ Δ, ψ.eval v = true) : ∃ ψ ∈ A :: Δ, ψ.eval v = true := by
  obtain ⟨ψ, hψ, hv⟩ := h; exact ⟨ψ, List.mem_cons_of_mem _ hψ, hv⟩

theorem ex_head {v : α → Bool} {Δ : List (Formula α)} {A : Formula α}
    (h : A.eval v = true) : ∃ ψ ∈ A :: Δ, ψ.eval v = true :=
  ⟨A, List.mem_cons_self .., h⟩

theorem ex_of_rest {v : α → Bool} {Δ : List (Formula α)} {φ : Formula α}
    (h : ∃ ψ ∈ rest Δ φ, ψ.eval v = true) : ∃ ψ ∈ Δ, ψ.eval v = true := by
  obtain ⟨ψ, hψ, hv⟩ := h; exact ⟨ψ, (mem_rest.mp hψ).1, hv⟩

/-- A classically valid atomic sequent shares an atom. -/
theorem valid_atomic_overlap {Γ Δ : List (Formula α)} (hg : allAtomic Γ = true)
    (hd : allAtomic Δ = true) (hv : Valid Γ Δ) : ∃ a, atom a ∈ Γ ∧ atom a ∈ Δ := by
  rw [allAtomic_iff] at hg hd
  obtain ⟨ψ, hψ, ht⟩ := hv (fun a => decide (atom a ∈ Γ)) (by
    intro φ hφ
    obtain ⟨a, rfl⟩ := isAtom_iff.mp (hg φ hφ)
    simp [Formula.eval, hφ])
  obtain ⟨b, rfl⟩ := isAtom_iff.mp (hd ψ hψ)
  exact ⟨b, by simpa [Formula.eval] using ht, hψ⟩

/-- **Supraclassicality.** Over every base, every classically valid sequent is
derivable. -/
theorem supraclassical (R : BaseRel α) {Γ Δ : List (Formula α)} (h : Valid Γ Δ) :
    Derivable R Γ Δ := by
  refine derivable_of_preserved R Valid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (measure Γ Δ + 1) Γ Δ (by omega) h
  · intro Γ Δ hg hd hv
    exact Derivable.ax hg hd (Or.inl (valid_atomic_overlap hg hd hv))
  · -- L¬
    intro Γ Δ A _ H v hv
    cases hA : A.eval v
    · exact ex_cons A (H v (all_of_rest hv (by simp [Formula.eval, hA])))
    · exact ex_head hA
  · -- L→
    intro Γ Δ A B _ H
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      cases hA : A.eval v
      · exact ex_cons A (H v (all_of_rest hv (by simp [Formula.eval, hA])))
      · exact ex_head hA
    · intro v hv
      have hB := hv B (List.mem_cons_self ..)
      exact H v (all_of_rest (fun x hx => hv x (List.mem_cons_of_mem _ hx))
        (by simp [Formula.eval, hB]))
    · intro v hv
      have hB := hv B (List.mem_cons_self ..)
      exact ex_cons A (H v (all_of_rest (fun x hx => hv x (List.mem_cons_of_mem _ hx))
        (by simp [Formula.eval, hB])))
  · -- L∧
    intro Γ Δ A B _ H v hv
    have hA := hv A (by simp)
    have hB := hv B (by simp)
    exact H v (all_of_rest (φ := conj A B) (fun x hx => hv x (by simp [hx]))
      (by simp [Formula.eval, hA, hB]))
  · -- L∨
    intro Γ Δ A B _ H
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      have hA := hv A (by simp)
      exact H v (all_of_rest (φ := disj A B) (fun x hx => hv x (by simp [hx]))
        (by simp [Formula.eval, hA]))
    · intro v hv
      have hB := hv B (by simp)
      exact H v (all_of_rest (φ := disj A B) (fun x hx => hv x (by simp [hx]))
        (by simp [Formula.eval, hB]))
    · intro v hv
      have hA := hv A (by simp)
      exact H v (all_of_rest (φ := disj A B) (fun x hx => hv x (by simp [hx]))
        (by simp [Formula.eval, hA]))
  · -- R¬
    intro Γ Δ A _ H v hv
    have hA := hv A (by simp)
    rcases pick (neg A) (H v (fun x hx => hv x (by simp [hx]))) with h | h
    · simp [Formula.eval, hA] at h
    · exact h
  · -- R→
    intro Γ Δ A B _ H v hv
    have hA := hv A (by simp)
    rcases pick (impl A B) (H v (fun x hx => hv x (by simp [hx]))) with h | h
    · exact ex_head (by simpa [Formula.eval, hA] using h)
    · exact ex_cons B h
  · -- R∧
    intro Γ Δ A B _ H
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      rcases pick (conj A B) (H v hv) with h | h
      · exact ex_head (by simp [Formula.eval] at h; exact h.1)
      · exact ex_cons A h
    · intro v hv
      rcases pick (conj A B) (H v hv) with h | h
      · exact ex_head (by simp [Formula.eval] at h; exact h.2)
      · exact ex_cons B h
    · intro v hv
      rcases pick (conj A B) (H v hv) with h | h
      · exact ex_head (by simp [Formula.eval] at h; exact h.1)
      · exact ex_cons A (ex_cons B h)
  · -- R∨
    intro Γ Δ A B _ H v hv
    rcases pick (disj A B) (H v hv) with h | h
    · simp only [Formula.eval, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ex_head h
      · exact ex_cons A (ex_head h)
    · exact ex_cons A (ex_cons B h)

/-- The empty base: no base consequences beyond Containment. -/
def emptyBase : BaseRel α := fun _ _ => false

/-- **Soundness for the empty base.** With Containment only, every derivable
sequent is classically valid. -/
theorem emptyBase_sound {Γ Δ : List (Formula α)} (h : Derivable emptyBase Γ Δ) :
    Valid Γ Δ := by
  induction h with
  | ax _ _ hor =>
    rcases hor with ⟨a, h1, h2⟩ | hb
    · intro v hv; exact ⟨atom a, h2, hv _ h1⟩
    · simp [emptyBase] at hb
  | @negL Γ Δ A hm _ ih =>
    intro v hv
    have hn := hv _ hm
    obtain ⟨ψ, hψ, ht⟩ := ih v (fun x hx => hv x (mem_rest.mp hx).1)
    rcases List.mem_cons.mp hψ with e | e
    · subst e; simp [Formula.eval, ht] at hn
    · exact ⟨ψ, e, ht⟩
  | @implL Γ Δ A B hm _ _ _ ih1 ih2 _ =>
    intro v hv
    have hi := hv _ hm
    cases hA : A.eval v
    · obtain ⟨ψ, hψ, ht⟩ := ih1 v (fun x hx => hv x (mem_rest.mp hx).1)
      rcases List.mem_cons.mp hψ with e | e
      · subst e; rw [hA] at ht; cases ht
      · exact ⟨ψ, e, ht⟩
    · have hB : B.eval v = true := by simpa [Formula.eval, hA] using hi
      exact ih2 v (by
        intro x hx
        rcases List.mem_cons.mp hx with e | e
        · subst e; exact hB
        · exact hv x (mem_rest.mp e).1)
  | @conjL Γ Δ A B hm _ ih =>
    intro v hv
    have hc := hv _ hm
    simp only [Formula.eval, Bool.and_eq_true] at hc
    exact ih v (by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with e | e | e
      · subst e; exact hc.1
      · subst e; exact hc.2
      · exact hv x (mem_rest.mp e).1)
  | @disjL Γ Δ A B hm _ _ _ ih1 ih2 _ =>
    intro v hv
    have hc := hv _ hm
    simp only [Formula.eval, Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · exact ih1 v (by
        intro x hx
        rcases List.mem_cons.mp hx with e | e
        · subst e; exact hc
        · exact hv x (mem_rest.mp e).1)
    · exact ih2 v (by
        intro x hx
        rcases List.mem_cons.mp hx with e | e
        · subst e; exact hc
        · exact hv x (mem_rest.mp e).1)
  | @negR Γ Δ A hm _ ih =>
    intro v hv
    cases hA : A.eval v
    · exact ⟨_, hm, by simp [Formula.eval, hA]⟩
    · exact ex_of_rest (ih v (by
        intro x hx
        rcases List.mem_cons.mp hx with e | e
        · subst e; exact hA
        · exact hv x e))
  | @implR Γ Δ A B hm _ ih =>
    intro v hv
    cases hA : A.eval v
    · exact ⟨_, hm, by simp [Formula.eval, hA]⟩
    · obtain ⟨ψ, hψ, ht⟩ := ih v (by
        intro x hx
        rcases List.mem_cons.mp hx with e | e
        · subst e; exact hA
        · exact hv x e)
      rcases List.mem_cons.mp hψ with e | e
      · subst e; exact ⟨_, hm, by simp [Formula.eval, ht]⟩
      · exact ⟨ψ, (mem_rest.mp e).1, ht⟩
  | @conjR Γ Δ A B hm _ _ _ ih1 ih2 _ =>
    intro v hv
    obtain ⟨ψ1, hψ1, ht1⟩ := ih1 v hv
    obtain ⟨ψ2, hψ2, ht2⟩ := ih2 v hv
    rcases List.mem_cons.mp hψ1 with e1 | e1
    · rcases List.mem_cons.mp hψ2 with e2 | e2
      · subst e1; subst e2; exact ⟨_, hm, by simp [Formula.eval, ht1, ht2]⟩
      · exact ⟨ψ2, (mem_rest.mp e2).1, ht2⟩
    · exact ⟨ψ1, (mem_rest.mp e1).1, ht1⟩
  | @disjR Γ Δ A B hm _ ih =>
    intro v hv
    obtain ⟨ψ, hψ, ht⟩ := ih v hv
    simp only [List.mem_cons] at hψ
    rcases hψ with e | e | e
    · subst e; exact ⟨_, hm, by simp [Formula.eval, ht]⟩
    · subst e; exact ⟨_, hm, by simp [Formula.eval, ht]⟩
    · exact ⟨ψ, (mem_rest.mp e).1, ht⟩

/-- **The empty base is classical logic** (the book's Prop. 25, as reported):
over Containment alone, NMMS derives exactly the classically valid sequents. -/
theorem emptyBase_iff_valid (Γ Δ : List (Formula α)) :
    Derivable emptyBase Γ Δ ↔ Valid Γ Δ :=
  ⟨emptyBase_sound, supraclassical emptyBase⟩

end NMMS
