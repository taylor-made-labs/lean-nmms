/-
  LeanNmms.Refute

  Two uses of invertibility (`LeanNmms.Invertibility`):

  1. **"Not derivable" certificates.** A refutation is one failing branch: a
     list of steps, each naming a side, a principal sentence on that side, and
     which of its rule's premises to follow, ending at an atomic sequent that
     is not an axiom (no shared atom, not in the base). `refute` checks it in
     one pass, with no search; `refute_sound` proves that a refutation that
     checks shows the sequent is not derivable. Its length is at most the
     connective count. Soundness needs invertibility: a derivable conclusion
     would make the chosen premise derivable too, down to the leaf.

  2. **A search that never backtracks.** `fastN` decomposes the first complex
     sentence it finds (left side first) and never tries another choice:
     by invertibility, the conclusion is derivable exactly when all of that
     rule's premises are. It keeps pyNMMS's axiom shortcuts (`axiomCheck`) at
     every node. `fastProve_iff` proves it decides derivability. It has no
     memo table, so its cost is the size of one decomposition tree, with no
     factor for the choice of principal sentence.

  `findRefute` builds the refutation for an underivable sequent (it is not
  proved correct; its output is checked by `refute`, which is).
-/
import LeanNmms.Invertibility
import LeanNmms.Decide

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- The side a rule works on: `true` = left (antecedent). -/
def side (b : Bool) (Γ Δ : List (Formula α)) : List (Formula α) := if b then Γ else Δ

/-- The premises of the rule on `φ` on side `b`, as the calculus states them
(empty for an atom, which has no rule). -/
def premises : Bool → Formula α → List (Formula α) → List (Formula α) →
    List (List (Formula α) × List (Formula α))
  | _, atom _, _, _ => []
  | true, neg A, Γ, Δ => [(rest Γ (neg A), A :: Δ)]
  | true, impl A B, Γ, Δ => [(rest Γ (impl A B), A :: Δ), (B :: rest Γ (impl A B), Δ),
      (B :: rest Γ (impl A B), A :: Δ)]
  | true, conj A B, Γ, Δ => [(A :: B :: rest Γ (conj A B), Δ)]
  | true, disj A B, Γ, Δ => [(A :: rest Γ (disj A B), Δ), (B :: rest Γ (disj A B), Δ),
      (A :: B :: rest Γ (disj A B), Δ)]
  | false, neg A, Γ, Δ => [(A :: Γ, rest Δ (neg A))]
  | false, impl A B, Γ, Δ => [(A :: Γ, B :: rest Δ (impl A B))]
  | false, conj A B, Γ, Δ => [(Γ, A :: rest Δ (conj A B)), (Γ, B :: rest Δ (conj A B)),
      (Γ, A :: B :: rest Δ (conj A B))]
  | false, disj A B, Γ, Δ => [(Γ, A :: B :: rest Δ (disj A B))]

variable {R : BaseRel α}

/-- The rule is sound: all premises derivable gives the conclusion. -/
theorem premises_sound {b : Bool} {φ : Formula α} {Γ Δ : List (Formula α)}
    (hm : φ ∈ side b Γ Δ) (hna : φ.isAtom = false)
    (h : ∀ p ∈ premises b φ Γ Δ, Derivable R p.1 p.2) : Derivable R Γ Δ := by
  cases b <;> cases φ <;> simp only [side, Bool.false_eq_true, ite_false, ite_true] at hm <;>
    simp only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h
  all_goals first
    | exact Derivable.negL hm h
    | exact Derivable.negR hm h
    | exact Derivable.conjL hm h
    | exact Derivable.disjR hm h
    | exact Derivable.implR hm h
    | exact Derivable.implL hm h.1 h.2.1 h.2.2
    | exact Derivable.disjL hm h.1 h.2.1 h.2.2
    | exact Derivable.conjR hm h.1 h.2.1 h.2.2
    | simp [Formula.isAtom] at hna

/-- The rule is invertible: a derivable conclusion makes every premise
derivable (this is `invertibility`, restated per rule). -/
theorem premises_inv (hR : R.SetInvariant) {b : Bool} {φ : Formula α}
    {Γ Δ : List (Formula α)} (hm : φ ∈ side b Γ Δ) (hd : Derivable R Γ Δ) :
    ∀ p ∈ premises b φ Γ Δ, Derivable R p.1 p.2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := invertibility R hR Γ Δ hd
  cases b <;> cases φ <;> simp only [side, Bool.false_eq_true, ite_false, ite_true] at hm <;>
    simp only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.not_mem_nil, false_imp_iff, implies_true]
  · exact h5 _ hm
  · exact h7 _ _ hm
  · exact h8 _ _ hm
  · exact h6 _ _ hm
  · exact h1 _ hm
  · exact h3 _ _ hm
  · exact h4 _ _ hm
  · exact h2 _ _ hm

/-- Every premise is lighter than the conclusion. -/
theorem premises_measure {b : Bool} {φ : Formula α} {Γ Δ : List (Formula α)}
    (hm : φ ∈ side b Γ Δ) : ∀ p ∈ premises b φ Γ Δ, measure p.1 p.2 < measure Γ Δ := by
  cases b <;> cases φ <;> simp only [side, Bool.false_eq_true, ite_false, ite_true] at hm <;>
    simp only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, false_imp_iff, implies_true] <;>
    have hw := weight_rest hm <;>
    (try refine ⟨?_, ?_, ?_⟩) <;> meas

/-- An atomic sequent is derivable only as an axiom. -/
theorem derivable_atomic {Γ Δ : List (Formula α)} (hg : allAtomic Γ = true)
    (hd : allAtomic Δ = true) (h : Derivable R Γ Δ) :
    (∃ a, atom a ∈ Γ ∧ atom a ∈ Δ) ∨ R (atomsOf Γ) (atomsOf Δ) = true := by
  cases h with
  | ax _ _ hor => exact hor
  | negL hm _ => have := allAtomic_iff.mp hg _ hm; simp [Formula.isAtom] at this
  | implL hm _ _ _ => have := allAtomic_iff.mp hg _ hm; simp [Formula.isAtom] at this
  | conjL hm _ => have := allAtomic_iff.mp hg _ hm; simp [Formula.isAtom] at this
  | disjL hm _ _ _ => have := allAtomic_iff.mp hg _ hm; simp [Formula.isAtom] at this
  | negR hm _ => have := allAtomic_iff.mp hd _ hm; simp [Formula.isAtom] at this
  | implR hm _ => have := allAtomic_iff.mp hd _ hm; simp [Formula.isAtom] at this
  | conjR hm _ _ _ => have := allAtomic_iff.mp hd _ hm; simp [Formula.isAtom] at this
  | disjR hm _ => have := allAtomic_iff.mp hd _ hm; simp [Formula.isAtom] at this

/-! ### "Not derivable" certificates -/

/-- One step of a failing branch: the side and principal sentence of a rule,
and which of its premises (0, 1 or 2) the branch follows. -/
structure Step (α : Type) where
  left : Bool
  φ : Formula α
  idx : Nat
  deriving Repr

/-- An atomic sequent's axiom test: a shared atom, or in the base. -/
def atomicAx (R : BaseRel α) (Γ Δ : List (Formula α)) : Bool :=
  (atomsOf Γ).any (fun a => (atomsOf Δ).contains a) || R (atomsOf Γ) (atomsOf Δ)

/-- The refutation checker: follow the steps, recomputing each premise, and
require an atomic non-axiom at the end. -/
def refute (R : BaseRel α) : List (Step α) → List (Formula α) → List (Formula α) → Bool
  | [], Γ, Δ => allAtomic Γ && allAtomic Δ && !atomicAx R Γ Δ
  | s :: cs, Γ, Δ => (side s.left Γ Δ).contains s.φ &&
      match (premises s.left s.φ Γ Δ)[s.idx]? with
      | some p => refute R cs p.1 p.2
      | none => false

/-- **Refutation soundness**: a refutation that checks shows the sequent is
not derivable, over every set-invariant base. -/
theorem refute_sound (hR : R.SetInvariant) :
    ∀ (c : List (Step α)) (Γ Δ : List (Formula α)), refute R c Γ Δ = true →
      ¬ Derivable R Γ Δ
  | [], Γ, Δ, h, hd => by
    simp only [refute, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hg, hdd⟩, hn⟩ := h
    have := derivable_atomic hg hdd hd
    simp only [atomicAx, Bool.or_eq_false_iff, List.any_eq_false, List.contains_iff_mem,
      mem_atomsOf] at hn
    rcases this with ⟨a, h1, h2⟩ | hb
    · exact hn.1 a h1 h2
    · rw [hn.2] at hb; exact absurd hb (by simp)
  | s :: cs, Γ, Δ, h, hd => by
    simp only [refute, Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨hm, h⟩ := h
    split at h
    · rename_i p hp
      exact refute_sound hR cs _ _ h (premises_inv hR hm hd p (List.mem_of_getElem? hp))
    · simp at h

/-! ### The non-backtracking search -/

/-- The first complex sentence, left side first. -/
def pickComplex (Γ Δ : List (Formula α)) : Option (Bool × Formula α) :=
  match Γ.find? (fun φ => !φ.isAtom) with
  | some φ => some (true, φ)
  | none => (Δ.find? (fun φ => !φ.isAtom)).map (fun φ => (false, φ))

theorem pickComplex_some {Γ Δ : List (Formula α)} {b : Bool} {φ : Formula α}
    (h : pickComplex Γ Δ = some (b, φ)) : φ ∈ side b Γ Δ ∧ φ.isAtom = false := by
  unfold pickComplex at h
  split at h
  · rename_i ψ hψ
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := List.find?_some hψ
    exact ⟨List.mem_of_find?_eq_some hψ, by simpa using this⟩
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨ψ, hψ, rfl, rfl⟩ := h
    have := List.find?_some hψ
    exact ⟨List.mem_of_find?_eq_some hψ, by simpa using this⟩

theorem pickComplex_none {Γ Δ : List (Formula α)} (h : pickComplex Γ Δ = none) :
    allAtomic Γ = true ∧ allAtomic Δ = true := by
  unfold pickComplex at h
  split at h
  · simp at h
  · rename_i hΓ
    simp only [Option.map_eq_none_iff] at h
    simp only [List.find?_eq_none, Bool.not_eq_true', Bool.not_eq_false] at hΓ h
    exact ⟨allAtomic_iff.mpr hΓ, allAtomic_iff.mpr h⟩

/-- Search with fuel, never backtracking over the choice of principal sentence. -/
def fastN (R : BaseRel α) : Nat → List (Formula α) → List (Formula α) → Bool
  | 0, _, _ => false
  | n + 1, Γ, Δ =>
    axiomCheck R Γ Δ ||
      match pickComplex Γ Δ with
      | some (b, φ) => (premises b φ Γ Δ).all (fun p => fastN R n p.1 p.2)
      | none => false

/-- The fast decision procedure: fuel one above the connective count. -/
def fastProve (R : BaseRel α) (Γ Δ : List (Formula α)) : Bool :=
  fastN R (measure Γ Δ + 1) Γ Δ

theorem fastN_sound : ∀ n (Γ Δ : List (Formula α)), fastN R n Γ Δ = true → Derivable R Γ Δ
  | 0, _, _, h => by simp [fastN] at h
  | n + 1, Γ, Δ, h => by
    simp only [fastN, Bool.or_eq_true] at h
    rcases h with h | h
    · exact axiomCheck_sound h
    · split at h
      · rename_i b φ hp
        obtain ⟨hm, hna⟩ := pickComplex_some hp
        exact premises_sound hm hna (fun p hpm => fastN_sound n _ _ (List.all_eq_true.mp h p hpm))
      · simp at h

theorem fastN_complete (hR : R.SetInvariant) :
    ∀ n (Γ Δ : List (Formula α)), measure Γ Δ < n → Derivable R Γ Δ → fastN R n Γ Δ = true
  | 0, _, _, hn, _ => absurd hn (by omega)
  | n + 1, Γ, Δ, hn, hd => by
    simp only [fastN, Bool.or_eq_true]
    by_cases hax : axiomCheck R Γ Δ = true
    · exact Or.inl hax
    · right
      split
      · rename_i b φ hp
        obtain ⟨hm, _⟩ := pickComplex_some hp
        apply List.all_eq_true.mpr
        intro p hpm
        have := premises_measure hm p hpm
        exact fastN_complete hR n _ _ (by omega) (premises_inv hR hm hd p hpm)
      · rename_i hp
        obtain ⟨hg, hdd⟩ := pickComplex_none hp
        exfalso; apply hax
        simp only [axiomCheck, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
          List.contains_iff_mem]
        rcases derivable_atomic hg hdd hd with ⟨a, h1, h2⟩ | hb
        · left; right; exact ⟨atom a, h1, rfl, h2⟩
        · right; exact ⟨⟨hg, hdd⟩, hb⟩

/-- **The non-backtracking search is correct** over every set-invariant base. -/
theorem fastProve_iff (hR : R.SetInvariant) (Γ Δ : List (Formula α)) :
    fastProve R Γ Δ = true ↔ Derivable R Γ Δ :=
  ⟨fastN_sound _ Γ Δ, fun h => fastN_complete hR _ Γ Δ (by omega) h⟩

/-- Build a failing branch (unverified; `refute` checks the result). -/
def findRefuteN (R : BaseRel α) : Nat → List (Formula α) → List (Formula α) →
    Option (List (Step α))
  | 0, _, _ => none
  | n + 1, Γ, Δ =>
    if axiomCheck R Γ Δ then none else
    match pickComplex Γ Δ with
    | none => some []
    | some (b, φ) =>
      (premises b φ Γ Δ).zipIdx.findSome? (fun pi =>
        (findRefuteN R n pi.1.1 pi.1.2).map (fun c => ⟨b, φ, pi.2⟩ :: c))

def findRefute (R : BaseRel α) (Γ Δ : List (Formula α)) : Option (List (Step α)) :=
  findRefuteN R (measure Γ Δ + 1) Γ Δ

end NMMS
