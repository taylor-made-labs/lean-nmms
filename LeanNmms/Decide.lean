/-
  LeanNmms.Decide

  The two decision procedures and their correctness: each returns `true`
  exactly on the sequents that NMMS derives from the supplied base.

  * `axiomCheck` is the only axiom test: an atomic sequent in the base. There
    are no other shortcuts. (pyNMMS's `_is_axiom` also accepts any sequent
    whose sides share a sentence; that is Containment, which NMMS does not
    assume, so it is not used here.)
  * `fastProve` (the default of `nmms-lean`) decomposes the first complex
    sentence it finds (left side first) and never tries another choice: by
    invertibility, the conclusion is derivable exactly when all of that rule's
    premises are. Its cost is the size of one decomposition tree.
  * `prove` is root-first search over *every* choice of principal sentence,
    as pyNMMS's `NMMSReasoner._prove` searches (pyNMMS tries the left
    sentences, then the right ones, sorted by their text; the order cannot
    change a Boolean "exists", so it is not modelled).
  * Both always remove the principal sentence from its side. The book's rules
    also have instances whose context keeps it; `invertibility` shows that
    they derive nothing more, which is why completeness holds against the
    book's `Derivable`.
  * Both are written with explicit fuel `n` so that they are structurally
    recursive (the kernel can evaluate them, which `decide` uses for the
    examples). Fuel is not a limit in practice: each is called with
    `measure Γ Δ + 1`, and any fuel above the connective count gives the
    same answer (`proveN_stable` for `prove`; for `fastN` it follows from
    `fastN_sound` and `fastN_complete`). That is the termination result:
    proof depth is bounded by the connective count.
-/
import LeanNmms.Invertibility
import LeanNmms.Base

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- The axiom test: the sequent is atomic and in the base. -/
def axiomCheck (R : BaseRel α) (Γ Δ : List (Formula α)) : Bool :=
  allAtomic Γ && allAtomic Δ && R (atomsOf Γ) (atomsOf Δ)

theorem axiomCheck_iff {R : BaseRel α} {Γ Δ : List (Formula α)} :
    axiomCheck R Γ Δ = true ↔
      allAtomic Γ = true ∧ allAtomic Δ = true ∧ R (atomsOf Γ) (atomsOf Δ) = true := by
  simp [axiomCheck, and_assoc]

/-- The axiom test is sound: it accepts only axioms. -/
theorem axiomCheck_sound {R : BaseRel α} {Γ Δ : List (Formula α)}
    (h : axiomCheck R Γ Δ = true) : Derivable R Γ Δ := by
  obtain ⟨hg, hd, hb⟩ := axiomCheck_iff.mp h
  exact Derivable.ax hg hd hb

/-- The side a rule works on: `true` = left (antecedent). -/
def side (b : Bool) (Γ Δ : List (Formula α)) : List (Formula α) := if b then Γ else Δ

/-- The premises of the rule on `φ` on side `b`, with `φ` removed from its side
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
    | exact Derivable.negL_rest hm h
    | exact Derivable.negR_rest hm h
    | exact Derivable.conjL_rest hm h
    | exact Derivable.disjR_rest hm h
    | exact Derivable.implR_rest hm h
    | exact Derivable.implL_rest hm h.1 h.2.1 h.2.2
    | exact Derivable.disjL_rest hm h.1 h.2.1 h.2.2
    | exact Derivable.conjR_rest hm h.1 h.2.1 h.2.2
    | simp [Formula.isAtom] at hna

/-- The rule is invertible: a derivable conclusion makes every premise
derivable (`invertibility`, per rule). -/
theorem premises_inv (hR : R.SetInvariant) {b : Bool} {φ : Formula α}
    {Γ Δ : List (Formula α)} (hm : φ ∈ side b Γ Δ) (hd : Derivable R Γ Δ) :
    ∀ p ∈ premises b φ Γ Δ, Derivable R p.1 p.2 := by
  cases b <;> cases φ <;> simp only [side, Bool.false_eq_true, ite_false, ite_true] at hm <;>
    simp only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.not_mem_nil, false_imp_iff, implies_true]
  · exact negR_inv hR hm hd
  · exact conjR_inv hR hm hd
  · exact disjR_inv hR hm hd
  · exact implR_inv hR hm hd
  · exact negL_inv hR hm hd
  · exact conjL_inv hR hm hd
  · exact disjL_inv hR hm hd
  · exact implL_inv hR hm hd

/-- Every premise is lighter than the conclusion. -/
theorem premises_measure {b : Bool} {φ : Formula α} {Γ Δ : List (Formula α)}
    (hm : φ ∈ side b Γ Δ) : ∀ p ∈ premises b φ Γ Δ, measure p.1 p.2 < measure Γ Δ := by
  cases b <;> cases φ <;> simp only [side, Bool.false_eq_true, ite_false, ite_true] at hm <;>
    simp only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, false_imp_iff, implies_true] <;>
    have hw := weight_rest hm <;>
    (try refine ⟨?_, ?_, ?_⟩) <;> meas

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
    match pickComplex Γ Δ with
    | some (b, φ) => (premises b φ Γ Δ).all (fun p => fastN R n p.1 p.2)
    | none => axiomCheck R Γ Δ

/-- The default decision procedure: fuel one above the connective count. -/
def fastProve (R : BaseRel α) (Γ Δ : List (Formula α)) : Bool :=
  fastN R (measure Γ Δ + 1) Γ Δ

theorem fastN_sound : ∀ n (Γ Δ : List (Formula α)), fastN R n Γ Δ = true → Derivable R Γ Δ
  | 0, _, _, h => by simp [fastN] at h
  | n + 1, Γ, Δ, h => by
    simp only [fastN] at h
    split at h
    · rename_i b φ hp
      obtain ⟨hm, hna⟩ := pickComplex_some hp
      exact premises_sound hm hna (fun p hpm => fastN_sound n _ _ (List.all_eq_true.mp h p hpm))
    · exact axiomCheck_sound h

theorem fastN_complete (hR : R.SetInvariant) :
    ∀ n (Γ Δ : List (Formula α)), measure Γ Δ < n → Derivable R Γ Δ → fastN R n Γ Δ = true
  | 0, _, _, hn, _ => absurd hn (by omega)
  | n + 1, Γ, Δ, hn, hd => by
    simp only [fastN]
    split
    · rename_i b φ hp
      obtain ⟨hm, _⟩ := pickComplex_some hp
      apply List.all_eq_true.mpr
      intro p hpm
      have := premises_measure hm p hpm
      exact fastN_complete hR n _ _ (by omega) (premises_inv hR hm hd p hpm)
    · rename_i hp
      obtain ⟨hg, hdd⟩ := pickComplex_none hp
      exact axiomCheck_iff.mpr ⟨hg, hdd, derivable_atomic hg hdd hd⟩

/-- **The default reasoner is correct**: over every set-invariant base,
`fastProve` returns `true` exactly on the sequents NMMS derives from that
base. -/
theorem fastProve_iff (hR : R.SetInvariant) (Γ Δ : List (Formula α)) :
    fastProve R Γ Δ = true ↔ Derivable R Γ Δ :=
  ⟨fastN_sound _ Γ Δ, fun h => fastN_complete hR _ Γ Δ (by omega) h⟩

/-! ### The backtracking search -/

/-- Try the rule on `φ` (side `b`); `p` decides premises. An atom has no rule. -/
def stepB (p : List (Formula α) → List (Formula α) → Bool) (b : Bool)
    (Γ Δ : List (Formula α)) (φ : Formula α) : Bool :=
  !φ.isAtom && (premises b φ Γ Δ).all (fun q => p q.1 q.2)

/-- Root-first proof search with fuel, over every choice of principal sentence. -/
def proveN (R : BaseRel α) : Nat → List (Formula α) → List (Formula α) → Bool
  | 0, _, _ => false
  | n + 1, Γ, Δ =>
    axiomCheck R Γ Δ || Γ.any (stepB (proveN R n) true Γ Δ) ||
      Δ.any (stepB (proveN R n) false Γ Δ)

/-- The backtracking decision procedure: fuel one above the connective count. -/
def prove (R : BaseRel α) (Γ Δ : List (Formula α)) : Bool :=
  proveN R (measure Γ Δ + 1) Γ Δ

/-- **Soundness** of the search (any fuel). -/
theorem proveN_sound : ∀ n (Γ Δ : List (Formula α)), proveN R n Γ Δ = true → Derivable R Γ Δ
  | 0, _, _, h => by simp [proveN] at h
  | n + 1, Γ, Δ, h => by
    simp only [proveN, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with (h | ⟨φ, hφ, h⟩) | ⟨φ, hφ, h⟩
    · exact axiomCheck_sound h
    · simp only [stepB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
      exact premises_sound (b := true) hφ h.1 (fun p hp => proveN_sound n _ _ (h.2 p hp))
    · simp only [stepB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
      exact premises_sound (b := false) hφ h.1 (fun p hp => proveN_sound n _ _ (h.2 p hp))

/-- What the fast search finds, the backtracking search finds (it tries the
same choice among others). -/
theorem proveN_of_fastN : ∀ n (Γ Δ : List (Formula α)), fastN R n Γ Δ = true →
    proveN R n Γ Δ = true
  | 0, _, _, h => by simp [fastN] at h
  | n + 1, Γ, Δ, h => by
    simp only [fastN] at h
    simp only [proveN, Bool.or_eq_true, List.any_eq_true]
    split at h
    · rename_i b φ hp
      obtain ⟨hm, hna⟩ := pickComplex_some hp
      have hs : stepB (proveN R n) b Γ Δ φ = true := by
        simp only [stepB, hna, Bool.not_false, Bool.true_and, List.all_eq_true]
        exact fun q hq => proveN_of_fastN n _ _ (List.all_eq_true.mp h q hq)
      cases b
      · exact Or.inr ⟨φ, hm, hs⟩
      · exact Or.inl (Or.inr ⟨φ, hm, hs⟩)
    · exact Or.inl (Or.inl h)

/-- **Completeness** of the search: a derivable sequent is found with any fuel
above its connective count. -/
theorem proveN_complete (hR : R.SetInvariant) {Γ Δ : List (Formula α)}
    (h : Derivable R Γ Δ) (n : Nat) (hn : measure Γ Δ < n) : proveN R n Γ Δ = true :=
  proveN_of_fastN n Γ Δ (fastN_complete hR n Γ Δ hn h)

/-- **The backtracking reasoner is correct**: over every set-invariant base,
`prove` returns `true` exactly on the sequents NMMS derives from that base. -/
theorem prove_iff (hR : R.SetInvariant) (Γ Δ : List (Formula α)) :
    prove R Γ Δ = true ↔ Derivable R Γ Δ :=
  ⟨proveN_sound _ Γ Δ, fun h => proveN_complete hR h _ (by omega)⟩

/-- **Termination / depth bound.** Search depth never needs to exceed the
connective count: every fuel above it gives the same answer. -/
theorem proveN_stable (hR : R.SetInvariant) (Γ Δ : List (Formula α)) (n : Nat)
    (hn : measure Γ Δ < n) : proveN R n Γ Δ = prove R Γ Δ := by
  cases h : prove R Γ Δ with
  | true => exact proveN_complete hR ((prove_iff hR Γ Δ).mp h) n hn
  | false =>
    cases h' : proveN R n Γ Δ with
    | false => rfl
    | true =>
      have := (prove_iff hR Γ Δ).mpr (proveN_sound n Γ Δ h')
      rw [h] at this; exact absurd this (by simp)

/-- **The reasoner over a pyNMMS base** (what `nmms-lean` runs): for every
list of entries `B`, both procedures accept exactly the sequents that NMMS
derives from the base `baseRel B`, with no consequence added or removed. -/
theorem reasoner_correct (B : List (Entry α)) (Γ Δ : List (Formula α)) :
    (fastProve (baseRel B) Γ Δ = true ↔ Derivable (baseRel B) Γ Δ) ∧
    (prove (baseRel B) Γ Δ = true ↔ Derivable (baseRel B) Γ Δ) :=
  ⟨fastProve_iff (baseRel_setInvariant B) Γ Δ, prove_iff (baseRel_setInvariant B) Γ Δ⟩

/-- Derivability over a set-invariant base is decidable. -/
def decidableDerivable (hR : R.SetInvariant) (Γ Δ : List (Formula α)) :
    Decidable (Derivable R Γ Δ) :=
  decidable_of_iff _ (fastProve_iff hR Γ Δ)

/-- Derivability over a pyNMMS base is decidable (the kernel can evaluate it
with `decide`, since `fastProve` is structurally recursive). -/
instance (B : List (Entry α)) (Γ Δ : List (Formula α)) :
    Decidable (Derivable (baseRel B) Γ Δ) :=
  decidableDerivable (baseRel_setInvariant B) Γ Δ

end NMMS
