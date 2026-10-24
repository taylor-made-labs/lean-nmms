/-
  LeanNmms.Containment

  1. A reusable induction principle, `decompose_of_preserved`: if a property
     `P` of sequents is kept by the premises of every rule, and a goal `Q`
     holds of atomic sequents with `P` and is closed under every rule (with the
     principal sentence removed from its side), then `P` implies `Q`
     everywhere. It is proved by induction on the total connective count, so
     it also shows that full decomposition always ends (the measure falls on
     every premise). `derivable_of_preserved` is the case `Q = Derivable`.
  2. Containment for every sentence (Reflexivity in the book's terms), *for a
     base that obeys Containment*: then `Γ ⇒ Δ` is derivable whenever the sides
     share any sentence, atomic or complex. Two forms: over a base with
     Containment for the atoms of a language `L` (`BaseRel.ContainmentOn L`,
     which any base gets by adding `coEntries L`, `containmentOn_coEntries`),
     a shared sentence whose atoms are all in `L` suffices,
     `overlap_derivable_on`; over a base with Containment for
     every atom (`BaseRel.Containment`), any shared sentence does,
     `overlap_derivable` (the case `L` = the sentence's atoms). NMMS does not
     assume the base obeys Containment, and without it these sequents need
     not be derivable (`emptyBase_underivable`: over the empty base not even
     `p ⇒ p` is).
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
premises of every rule applicable to it, and `Q` holds of atomic sequents with
`P` and is closed under every rule, then `Q` holds of the sequent. -/
theorem decompose_of_preserved
    (P Q : List (Formula α) → List (Formula α) → Prop)
    (hax : ∀ Γ Δ, allAtomic Γ = true → allAtomic Δ = true → P Γ Δ → Q Γ Δ)
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
    (hdisjR : ∀ Γ Δ A B, disj A B ∈ Δ → P Γ Δ → P Γ (A :: B :: rest Δ (disj A B)))
    (qnegL : ∀ Γ Δ A, neg A ∈ Γ → Q (rest Γ (neg A)) (A :: Δ) → Q Γ Δ)
    (qimplL : ∀ Γ Δ A B, impl A B ∈ Γ → Q (rest Γ (impl A B)) (A :: Δ) →
      Q (B :: rest Γ (impl A B)) Δ → Q (B :: rest Γ (impl A B)) (A :: Δ) → Q Γ Δ)
    (qconjL : ∀ Γ Δ A B, conj A B ∈ Γ → Q (A :: B :: rest Γ (conj A B)) Δ → Q Γ Δ)
    (qdisjL : ∀ Γ Δ A B, disj A B ∈ Γ → Q (A :: rest Γ (disj A B)) Δ →
      Q (B :: rest Γ (disj A B)) Δ → Q (A :: B :: rest Γ (disj A B)) Δ → Q Γ Δ)
    (qnegR : ∀ Γ Δ A, neg A ∈ Δ → Q (A :: Γ) (rest Δ (neg A)) → Q Γ Δ)
    (qimplR : ∀ Γ Δ A B, impl A B ∈ Δ → Q (A :: Γ) (B :: rest Δ (impl A B)) → Q Γ Δ)
    (qconjR : ∀ Γ Δ A B, conj A B ∈ Δ → Q Γ (A :: rest Δ (conj A B)) →
      Q Γ (B :: rest Δ (conj A B)) → Q Γ (A :: B :: rest Δ (conj A B)) → Q Γ Δ)
    (qdisjR : ∀ Γ Δ A B, disj A B ∈ Δ → Q Γ (A :: B :: rest Δ (disj A B)) → Q Γ Δ) :
    ∀ n Γ Δ, measure Γ Δ < n → P Γ Δ → Q Γ Δ := by
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
          exact qnegR _ _ _ hφ (ih _ _ (by meas) (hnegR _ _ _ hφ hP))
        | impl A B =>
          exact qimplR _ _ _ _ hφ (ih _ _ (by meas) (himplR _ _ _ _ hφ hP))
        | conj A B =>
          obtain ⟨h1, h2, h3⟩ := hconjR _ _ _ _ hφ hP
          exact qconjR _ _ _ _ hφ (ih _ _ (by meas) h1) (ih _ _ (by meas) h2)
            (ih _ _ (by meas) h3)
        | disj A B =>
          exact qdisjR _ _ _ _ hφ (ih _ _ (by meas) (hdisjR _ _ _ _ hφ hP))
    · obtain ⟨φ, hφ, hna⟩ := exists_complex hg
      have hw := weight_rest hφ
      cases φ with
      | atom a => simp [isAtom] at hna
      | neg A =>
        exact qnegL _ _ _ hφ (ih _ _ (by meas) (hnegL _ _ _ hφ hP))
      | impl A B =>
        obtain ⟨h1, h2, h3⟩ := himplL _ _ _ _ hφ hP
        exact qimplL _ _ _ _ hφ (ih _ _ (by meas) h1) (ih _ _ (by meas) h2)
          (ih _ _ (by meas) h3)
      | conj A B =>
        exact qconjL _ _ _ _ hφ (ih _ _ (by meas) (hconjL _ _ _ _ hφ hP))
      | disj A B =>
        obtain ⟨h1, h2, h3⟩ := hdisjL _ _ _ _ hφ hP
        exact qdisjL _ _ _ _ hφ (ih _ _ (by meas) h1) (ih _ _ (by meas) h2)
          (ih _ _ (by meas) h3)

/-- The decomposition principle with goal `Derivable R`: if `P` holds of a
sequent, is inherited by the premises of every rule, and gives derivability
on atomic sequents, then the sequent is derivable. -/
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
    ∀ n Γ Δ, measure Γ Δ < n → P Γ Δ → Derivable R Γ Δ :=
  decompose_of_preserved P (Derivable R) hax hnegL himplL hconjL hdisjL hnegR himplR hconjR
    hdisjR (fun _ _ _ h => Derivable.negL_rest h) (fun _ _ _ _ h => Derivable.implL_rest h)
    (fun _ _ _ _ h => Derivable.conjL_rest h) (fun _ _ _ _ h => Derivable.disjL_rest h)
    (fun _ _ _ h => Derivable.negR_rest h) (fun _ _ _ _ h => Derivable.implR_rest h)
    (fun _ _ _ _ h => Derivable.conjR_rest h) (fun _ _ _ _ h => Derivable.disjR_rest h)

/-- Over a base that obeys Containment for the atoms of `L`: a shared atom of
`L` makes a sequent derivable, whatever else is on the sides. -/
theorem atom_overlap_on {R : BaseRel α} {L : List α} (hC : R.ContainmentOn L) {a : α}
    (ha : a ∈ L) {Γ Δ : List (Formula α)} (h1 : atom a ∈ Γ) (h2 : atom a ∈ Δ) :
    Derivable R Γ Δ := by
  refine derivable_of_preserved R (fun Γ Δ => atom a ∈ Γ ∧ atom a ∈ Δ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (measure Γ Δ + 1) Γ Δ (by omega) ⟨h1, h2⟩
  · intro Γ Δ hg hd ⟨h1, h2⟩
    exact Derivable.ax hg hd (hC _ _ ⟨a, ha, mem_atomsOf.mpr h1, mem_atomsOf.mpr h2⟩)
  all_goals (intros; simp_all)

/-- **Containment for the sentences over `L`, over a base that obeys
Containment for the atoms of `L`**: a shared sentence whose atoms are all in
`L` makes a sequent derivable. -/
theorem overlap_derivable_on {R : BaseRel α} {L : List α} (hC : R.ContainmentOn L) :
    ∀ (φ : Formula α) {Γ Δ : List (Formula α)}, (∀ a ∈ φ.atoms, a ∈ L) →
      φ ∈ Γ → φ ∈ Δ → Derivable R Γ Δ := by
  intro φ
  induction φ with
  | atom a => intro Γ Δ hL h1 h2; exact atom_overlap_on hC (hL a (by simp)) h1 h2
  | neg A ih =>
    intro Γ Δ hL h1 h2
    refine Derivable.negL_rest h1 (Derivable.negR_rest (A := A) (by simp [h2]) ?_)
    exact ih (by simpa using hL) (by simp) (by simp [ne_neg A])
  | conj A B ihA ihB =>
    intro Γ Δ hL h1 h2
    have hA : ∀ a ∈ A.atoms, a ∈ L := fun a h => hL a (by simp [h])
    have hB : ∀ a ∈ B.atoms, a ∈ L := fun a h => hL a (by simp [h])
    refine Derivable.conjL_rest h1 (Derivable.conjR_rest h2 ?_ ?_ ?_)
    · exact ihA hA (by simp) (by simp)
    · exact ihB hB (by simp) (by simp)
    · exact ihA hA (by simp) (by simp)
  | disj A B ihA ihB =>
    intro Γ Δ hL h1 h2
    have hA : ∀ a ∈ A.atoms, a ∈ L := fun a h => hL a (by simp [h])
    have hB : ∀ a ∈ B.atoms, a ∈ L := fun a h => hL a (by simp [h])
    refine Derivable.disjL_rest h1 (Derivable.disjR_rest h2 ?_) (Derivable.disjR_rest h2 ?_)
      (Derivable.disjR_rest h2 ?_)
    · exact ihA hA (by simp) (by simp)
    · exact ihB hB (by simp) (by simp)
    · exact ihA hA (by simp) (by simp)
  | impl A B ihA ihB =>
    intro Γ Δ hL h1 h2
    have hA : ∀ a ∈ A.atoms, a ∈ L := fun a h => hL a (by simp [h])
    have hB : ∀ a ∈ B.atoms, a ∈ L := fun a h => hL a (by simp [h])
    refine Derivable.implL_rest h1 (Derivable.implR_rest (A := A) (B := B) (by simp [h2]) ?_)
      (Derivable.implR_rest h2 ?_) (Derivable.implR_rest (A := A) (B := B) (by simp [h2]) ?_)
    · exact ihA hA (by simp) (by simp [ne_impl_l A B])
    · exact ihB hB (by simp) (by simp)
    · exact ihB hB (by simp) (by simp)

/-- Over a base that obeys Containment: a shared atom makes a sequent
derivable, whatever else is on the sides. -/
theorem atom_overlap {R : BaseRel α} (hC : R.Containment) {a : α} {Γ Δ : List (Formula α)}
    (h1 : atom a ∈ Γ) (h2 : atom a ∈ Δ) : Derivable R Γ Δ :=
  atom_overlap_on (L := [a]) hC.on (List.mem_singleton_self a) h1 h2

/-- **Containment for all sentences, over a base that obeys Containment**: a
shared sentence makes a sequent derivable. -/
theorem overlap_derivable {R : BaseRel α} (hC : R.Containment) :
    ∀ (φ : Formula α) {Γ Δ : List (Formula α)}, φ ∈ Γ → φ ∈ Δ → Derivable R Γ Δ :=
  fun φ _ _ h1 h2 => overlap_derivable_on (L := φ.atoms) hC.on φ (fun _ h => h) h1 h2

end NMMS
