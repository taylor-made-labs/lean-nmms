/-
  LeanNmms.Classical

  NMMS and classical logic. NMMS takes its axioms from the base alone, so how
  much classical logic it derives depends on the base:

  * over the empty base it derives nothing (`emptyBase_underivable`,
    `LeanNmms.Calculus`), not even `p ⇒ p` or `⇒ p ∨ ¬p`;
  * over every base, everything it derives is classically valid as soon as
    the base's own sequents are (`valuation_sound`, for one valuation at a
    time);
  * over a base that obeys Containment for the atoms of a language `L`
    (`BaseRel.ContainmentOn L`) it derives every classically valid sequent
    whose atoms are all in `L` (supraclassicality; earlier versions of this
    file cited it as the book's Fact 2), `supraclassical_on`; over a base
    that obeys it for every atom (`BaseRel.Containment`), every classically
    valid sequent, `supraclassical`. The hypothesis is needed: it fails over
    the empty base;
  * a finite pyNMMS base supplies the first form: over `B ++ coEntries L`
    (any `B` plus a MONOTONE `a |~ a` per `a ∈ L`, `LeanNmms.Base`), every
    classically valid sequent whose atoms are in `L` is derivable,
    `supraclassical_coEntries`, and so is every sequent whose sides share a
    sentence over `L`, `overlap_derivable_coEntries`;
  * over the base whose only consequences are the Containment instances
    (`containmentBase`, for every atom) it derives exactly the classically
    valid sequents, `containmentBase_iff_valid`.

  Classical validity is the multi-succedent reading: every Boolean valuation
  that makes all of `Γ` true makes some member of `Δ` true.

  Proof idea. Supraclassicality uses the decomposition principle
  `derivable_of_preserved` with "classically valid, and every atom in `L`" as
  the preserved property: each rule's premises are valid when its conclusion
  is (the third premises included), their sentences are members of the
  conclusion's sides or parts of its principal sentence, and a valid atomic
  sequent must share an atom, here one of `L`, so it is in a base that obeys
  Containment for `L`. `supraclassical` is the case `L` = the sequent's atoms.
  Soundness is induction on derivations: each rule preserves truth under a
  valuation.
-/
import LeanNmms.Containment
import LeanNmms.Base

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

/-- Every atom of every sentence of `φ :: l` is in `L` if it holds for `φ`
and for `l`. -/
theorem atomsIn_cons {L : List α} {φ : Formula α} {l : List (Formula α)}
    (h1 : ∀ a ∈ φ.atoms, a ∈ L) (h2 : ∀ ψ ∈ l, ∀ a ∈ ψ.atoms, a ∈ L) :
    ∀ ψ ∈ φ :: l, ∀ a ∈ ψ.atoms, a ∈ L := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact h1
  · exact h2 ψ hψ

theorem atomsIn_rest {L : List α} {φ : Formula α} {l : List (Formula α)}
    (h : ∀ ψ ∈ l, ∀ a ∈ ψ.atoms, a ∈ L) : ∀ ψ ∈ rest l φ, ∀ a ∈ ψ.atoms, a ∈ L :=
  fun ψ hψ => h ψ (mem_rest.mp hψ).1

/-- Closes "every atom of every sentence of this premise side is in `L`": a
premise side is made of a side of the conclusion (perhaps minus the principal
sentence) and parts of the principal sentence, for which the context must
already have that fact. -/
macro "atoms_in" : tactic =>
  `(tactic| (repeat' (first | assumption | apply atomsIn_cons | apply atomsIn_rest)))

/-- **Supraclassicality, over a base that obeys Containment for the atoms of
`L`.** Every classically valid sequent whose atoms are all in `L` is
derivable. (Without Containment in the base this fails: over the empty base
nothing is derivable.) -/
theorem supraclassical_on {R : BaseRel α} {L : List α} (hC : R.ContainmentOn L)
    {Γ Δ : List (Formula α)} (hΓ : ∀ φ ∈ Γ, ∀ a ∈ φ.atoms, a ∈ L)
    (hΔ : ∀ φ ∈ Δ, ∀ a ∈ φ.atoms, a ∈ L) (h : Valid Γ Δ) : Derivable R Γ Δ := by
  refine derivable_of_preserved R (fun Γ Δ => Valid Γ Δ ∧ (∀ φ ∈ Γ, ∀ a ∈ φ.atoms, a ∈ L) ∧
      (∀ φ ∈ Δ, ∀ a ∈ φ.atoms, a ∈ L)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (measure Γ Δ + 1) Γ Δ (by omega) ⟨h, hΓ, hΔ⟩
  · intro Γ Δ hg hd ⟨hv, hgL, _⟩
    obtain ⟨a, h1, h2⟩ := valid_atomic_overlap hg hd hv
    exact Derivable.ax hg hd
      (hC _ _ ⟨a, hgL _ h1 a (by simp), mem_atomsOf.mpr h1, mem_atomsOf.mpr h2⟩)
  · -- L¬
    intro Γ Δ A hm ⟨H, hg, hd⟩
    have lA : ∀ a ∈ A.atoms, a ∈ L := fun a h => hg _ hm a (by simp [h])
    refine ⟨fun v hv => ?_, by atoms_in, by atoms_in⟩
    cases hA : A.eval v
    · exact ex_cons A (H v (all_of_rest hv (by simp [Formula.eval, hA])))
    · exact ex_head hA
  · -- L→
    intro Γ Δ A B hm ⟨H, hg, hd⟩
    have lA : ∀ a ∈ A.atoms, a ∈ L := fun a h => hg _ hm a (by simp [h])
    have lB : ∀ a ∈ B.atoms, a ∈ L := fun a h => hg _ hm a (by simp [h])
    refine ⟨⟨?_, by atoms_in, by atoms_in⟩, ⟨?_, by atoms_in, by atoms_in⟩,
      ⟨?_, by atoms_in, by atoms_in⟩⟩
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
    intro Γ Δ A B hm ⟨H, hg, hd⟩
    have lA : ∀ a ∈ A.atoms, a ∈ L := fun a h => hg _ hm a (by simp [h])
    have lB : ∀ a ∈ B.atoms, a ∈ L := fun a h => hg _ hm a (by simp [h])
    refine ⟨fun v hv => ?_, by atoms_in, by atoms_in⟩
    have hA := hv A (by simp)
    have hB := hv B (by simp)
    exact H v (all_of_rest (φ := conj A B) (fun x hx => hv x (by simp [hx]))
      (by simp [Formula.eval, hA, hB]))
  · -- L∨
    intro Γ Δ A B hm ⟨H, hg, hd⟩
    have lA : ∀ a ∈ A.atoms, a ∈ L := fun a h => hg _ hm a (by simp [h])
    have lB : ∀ a ∈ B.atoms, a ∈ L := fun a h => hg _ hm a (by simp [h])
    refine ⟨⟨?_, by atoms_in, by atoms_in⟩, ⟨?_, by atoms_in, by atoms_in⟩,
      ⟨?_, by atoms_in, by atoms_in⟩⟩
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
    intro Γ Δ A hm ⟨H, hg, hd⟩
    have lA : ∀ a ∈ A.atoms, a ∈ L := fun a h => hd _ hm a (by simp [h])
    refine ⟨fun v hv => ?_, by atoms_in, by atoms_in⟩
    have hA := hv A (by simp)
    rcases pick (neg A) (H v (fun x hx => hv x (by simp [hx]))) with h | h
    · simp [Formula.eval, hA] at h
    · exact h
  · -- R→
    intro Γ Δ A B hm ⟨H, hg, hd⟩
    have lA : ∀ a ∈ A.atoms, a ∈ L := fun a h => hd _ hm a (by simp [h])
    have lB : ∀ a ∈ B.atoms, a ∈ L := fun a h => hd _ hm a (by simp [h])
    refine ⟨fun v hv => ?_, by atoms_in, by atoms_in⟩
    have hA := hv A (by simp)
    rcases pick (impl A B) (H v (fun x hx => hv x (by simp [hx]))) with h | h
    · exact ex_head (by simpa [Formula.eval, hA] using h)
    · exact ex_cons B h
  · -- R∧
    intro Γ Δ A B hm ⟨H, hg, hd⟩
    have lA : ∀ a ∈ A.atoms, a ∈ L := fun a h => hd _ hm a (by simp [h])
    have lB : ∀ a ∈ B.atoms, a ∈ L := fun a h => hd _ hm a (by simp [h])
    refine ⟨⟨?_, by atoms_in, by atoms_in⟩, ⟨?_, by atoms_in, by atoms_in⟩,
      ⟨?_, by atoms_in, by atoms_in⟩⟩
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
    intro Γ Δ A B hm ⟨H, hg, hd⟩
    have lA : ∀ a ∈ A.atoms, a ∈ L := fun a h => hd _ hm a (by simp [h])
    have lB : ∀ a ∈ B.atoms, a ∈ L := fun a h => hd _ hm a (by simp [h])
    refine ⟨fun v hv => ?_, by atoms_in, by atoms_in⟩
    rcases pick (disj A B) (H v hv) with h | h
    · simp only [Formula.eval, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ex_head h
      · exact ex_cons A (ex_head h)
    · exact ex_cons A (ex_cons B h)

/-- **Supraclassicality, over a base that obeys Containment.** Every
classically valid sequent is derivable (`supraclassical_on`, with `L` the
atoms of the sequent). -/
theorem supraclassical {R : BaseRel α} (hC : R.Containment) {Γ Δ : List (Formula α)}
    (h : Valid Γ Δ) : Derivable R Γ Δ :=
  supraclassical_on (L := (Γ ++ Δ).flatMap Formula.atoms) hC.on
    (fun φ hφ _ ha => List.mem_flatMap.mpr ⟨φ, List.mem_append_left _ hφ, ha⟩)
    (fun φ hφ _ ha => List.mem_flatMap.mpr ⟨φ, List.mem_append_right _ hφ, ha⟩) h

/-! ### Truth under one valuation -/

theorem all_of_setEq {v : α → Bool} {Γ Γ₀ : List (Formula α)} {φ : Formula α}
    (e : SetEq Γ (φ :: Γ₀)) (h : ∀ x ∈ Γ, x.eval v = true) :
    φ.eval v = true ∧ ∀ x ∈ Γ₀, x.eval v = true :=
  ⟨h φ ((e φ).mpr (List.mem_cons_self ..)),
    fun x hx => h x ((e x).mpr (List.mem_cons_of_mem _ hx))⟩

theorem ex_of_setEq {v : α → Bool} {Δ Δ₀ : List (Formula α)} {φ : Formula α}
    (e : SetEq Δ (φ :: Δ₀)) (h : φ.eval v = true ∨ ∃ ψ ∈ Δ₀, ψ.eval v = true) :
    ∃ ψ ∈ Δ, ψ.eval v = true := by
  rcases h with h | ⟨ψ, hψ, ht⟩
  · exact ⟨φ, (e φ).mpr (List.mem_cons_self ..), h⟩
  · exact ⟨ψ, (e ψ).mpr (List.mem_cons_of_mem _ hψ), ht⟩

theorem cons_all {v : α → Bool} {Γ : List (Formula α)} {A : Formula α}
    (hA : A.eval v = true) (h : ∀ x ∈ Γ, x.eval v = true) : ∀ x ∈ A :: Γ, x.eval v = true := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hA
  · exact h x hx

/-- **Truth under one valuation.** If every base sequent is true under `v`,
then so is every derivable sequent: each rule preserves truth under `v`. -/
theorem valuation_sound (v : α → Bool) {R : BaseRel α}
    (hR : ∀ X Y, R X Y = true → (∀ x ∈ X, v x = true) → ∃ y ∈ Y, v y = true)
    {Γ Δ : List (Formula α)} (h : Derivable R Γ Δ) :
    (∀ φ ∈ Γ, φ.eval v = true) → ∃ ψ ∈ Δ, ψ.eval v = true := by
  induction h with
  | ax _ _ hb =>
    intro hv
    obtain ⟨y, hy, hvy⟩ := hR _ _ hb (fun x hx => by
      have := hv (atom x) (mem_atomsOf.mp hx); simpa [Formula.eval] using this)
    exact ⟨atom y, mem_atomsOf.mp hy, by simp [Formula.eval, hvy]⟩
  | @negL Γ Γ₀ Δ A e _ ih =>
    intro hv
    obtain ⟨hn, h0⟩ := all_of_setEq e hv
    obtain ⟨ψ, hψ, ht⟩ := ih h0
    rcases List.mem_cons.mp hψ with rfl | hψ
    · simp [Formula.eval, ht] at hn
    · exact ⟨ψ, hψ, ht⟩
  | @implL Γ Γ₀ Δ A B e _ _ _ ih1 ih2 _ =>
    intro hv
    obtain ⟨hi, h0⟩ := all_of_setEq e hv
    cases hA : A.eval v
    · obtain ⟨ψ, hψ, ht⟩ := ih1 h0
      rcases List.mem_cons.mp hψ with rfl | hψ
      · rw [hA] at ht; cases ht
      · exact ⟨ψ, hψ, ht⟩
    · have hB : B.eval v = true := by simpa [Formula.eval, hA] using hi
      exact ih2 (cons_all hB h0)
  | @conjL Γ Γ₀ Δ A B e _ ih =>
    intro hv
    obtain ⟨hc, h0⟩ := all_of_setEq e hv
    simp only [Formula.eval, Bool.and_eq_true] at hc
    exact ih (cons_all hc.1 (cons_all hc.2 h0))
  | @disjL Γ Γ₀ Δ A B e _ _ _ ih1 ih2 _ =>
    intro hv
    obtain ⟨hc, h0⟩ := all_of_setEq e hv
    simp only [Formula.eval, Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · exact ih1 (cons_all hc h0)
    · exact ih2 (cons_all hc h0)
  | @negR Γ Δ Δ₀ A e _ ih =>
    intro hv
    cases hA : A.eval v
    · exact ex_of_setEq e (Or.inl (by simp [Formula.eval, hA]))
    · exact ex_of_setEq e (Or.inr (ih (cons_all hA hv)))
  | @implR Γ Δ Δ₀ A B e _ ih =>
    intro hv
    cases hA : A.eval v
    · exact ex_of_setEq e (Or.inl (by simp [Formula.eval, hA]))
    · obtain ⟨ψ, hψ, ht⟩ := ih (cons_all hA hv)
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact ex_of_setEq e (Or.inl (by simp [Formula.eval, ht]))
      · exact ex_of_setEq e (Or.inr ⟨ψ, hψ, ht⟩)
  | @conjR Γ Δ Δ₀ A B e _ _ _ ih1 ih2 _ =>
    intro hv
    obtain ⟨ψ1, hψ1, ht1⟩ := ih1 hv
    obtain ⟨ψ2, hψ2, ht2⟩ := ih2 hv
    rcases List.mem_cons.mp hψ1 with rfl | e1
    · rcases List.mem_cons.mp hψ2 with rfl | e2
      · exact ex_of_setEq e (Or.inl (by simp [Formula.eval, ht1, ht2]))
      · exact ex_of_setEq e (Or.inr ⟨ψ2, e2, ht2⟩)
    · exact ex_of_setEq e (Or.inr ⟨ψ1, e1, ht1⟩)
  | @disjR Γ Δ Δ₀ A B e _ ih =>
    intro hv
    obtain ⟨ψ, hψ, ht⟩ := ih hv
    simp only [List.mem_cons] at hψ
    rcases hψ with rfl | rfl | hψ
    · exact ex_of_setEq e (Or.inl (by simp [Formula.eval, ht]))
    · exact ex_of_setEq e (Or.inl (by simp [Formula.eval, ht]))
    · exact ex_of_setEq e (Or.inr ⟨ψ, hψ, ht⟩)

/-- **Classical soundness.** If every base sequent is classically valid, every
derivable sequent is. -/
theorem classical_sound {R : BaseRel α}
    (hR : ∀ v : α → Bool, ∀ X Y, R X Y = true → (∀ x ∈ X, v x = true) → ∃ y ∈ Y, v y = true)
    {Γ Δ : List (Formula α)} (h : Derivable R Γ Δ) : Valid Γ Δ :=
  fun v => valuation_sound v (hR v) h

/-! ### The Containment base -/

/-- The base whose consequences are exactly the Containment instances: the
atomic sequents whose sides share an atom. -/
def containmentBase : BaseRel α := fun X Y => X.any (fun a => Y.contains a)

theorem containmentBase_iff {X Y : List α} :
    containmentBase X Y = true ↔ ∃ a, a ∈ X ∧ a ∈ Y := by
  simp [containmentBase]

theorem containmentBase_containment : (containmentBase : BaseRel α).Containment :=
  fun _ _ h => containmentBase_iff.mpr h

theorem containmentBase_setInvariant : (containmentBase : BaseRel α).SetInvariant := by
  intro a b a' b' ha hb
  rw [Bool.eq_iff_iff, containmentBase_iff, containmentBase_iff]
  exact ⟨fun ⟨x, h1, h2⟩ => ⟨x, (ha x).mp h1, (hb x).mp h2⟩,
    fun ⟨x, h1, h2⟩ => ⟨x, (ha x).mpr h1, (hb x).mpr h2⟩⟩

/-- **Classical logic is NMMS over the Containment base**: over the base whose
only consequences are the Containment instances, NMMS derives exactly the
classically valid sequents. -/
theorem containmentBase_iff_valid (Γ Δ : List (Formula α)) :
    Derivable containmentBase Γ Δ ↔ Valid Γ Δ := by
  refine ⟨classical_sound ?_, supraclassical containmentBase_containment⟩
  intro v X Y hb hX
  obtain ⟨a, h1, h2⟩ := containmentBase_iff.mp hb
  exact ⟨a, h2, hX a h1⟩

/-! ### Containment supplied in a pyNMMS base -/

/-- **Supraclassicality over `B` plus Containment for `L`**: over the pyNMMS
base `B ++ coEntries L` (`B` with a MONOTONE `a |~ a` for each `a ∈ L`),
every classically valid sequent whose atoms are all in `L` is derivable,
whatever `B` is. -/
theorem supraclassical_coEntries (B : List (Entry α)) (L : List α) {Γ Δ : List (Formula α)}
    (hΓ : ∀ φ ∈ Γ, ∀ a ∈ φ.atoms, a ∈ L) (hΔ : ∀ φ ∈ Δ, ∀ a ∈ φ.atoms, a ∈ L)
    (h : Valid Γ Δ) : Derivable (baseRel (B ++ coEntries L)) Γ Δ :=
  supraclassical_on (containmentOn_coEntries B L) hΓ hΔ h

/-- **Containment for the sentences over `L`, over `B` plus Containment for
`L`**: over the pyNMMS base `B ++ coEntries L`, a shared sentence whose atoms
are all in `L` makes a sequent derivable, whatever `B` is. -/
theorem overlap_derivable_coEntries (B : List (Entry α)) (L : List α) (φ : Formula α)
    {Γ Δ : List (Formula α)} (hL : ∀ a ∈ φ.atoms, a ∈ L) (h1 : φ ∈ Γ) (h2 : φ ∈ Δ) :
    Derivable (baseRel (B ++ coEntries L)) Γ Δ :=
  overlap_derivable_on (containmentOn_coEntries B L) φ hL h1 h2

end NMMS
