/-
  LeanNmms.Decide

  The decision procedure, written to mirror pyNMMS's `NMMSReasoner._prove`
  (with `max_depth = None`, its default), and its correctness.

  * `axiomCheck` is pyNMMS's `_is_axiom`: a shared complex sentence, or a
    shared atom, or (for an atomic sequent) a base match.
  * `proveN n` is root-first search: an axiom, or *some* complex sentence on
    the left, or *some* on the right, whose rule's premises all succeed. pyNMMS
    tries the left sentences, then the right ones, sorted by their text; the
    order cannot change a Boolean "exists", so it is not modelled.
  * The search is written with explicit fuel `n` so that it is structurally
    recursive (the kernel can evaluate it, which `decide` uses for the
    examples). Fuel is not a limit in practice: `prove` supplies
    `measure Γ Δ + 1`, and `proveN_stable` proves that any fuel above the
    connective count gives the same answer. That is the termination result:
    proof depth is bounded by the connective count, the claim pyNMMS's
    docstring makes.
  * pyNMMS's memo cache is not modelled. It only stores results already
    computed, so it cannot change answers if `Sequent` hashing and equality
    are content-based; the differential test exercises it.
-/
import LeanNmms.Containment

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- pyNMMS's `_is_axiom`. -/
def axiomCheck (R : BaseRel α) (Γ Δ : List (Formula α)) : Bool :=
  Γ.any (fun φ => !φ.isAtom && Δ.contains φ) ||
  Γ.any (fun φ => φ.isAtom && Δ.contains φ) ||
  (allAtomic Γ && allAtomic Δ && R (atomsOf Γ) (atomsOf Δ))

/-- Try the left rule whose principal sentence is `φ`; `p` decides premises. -/
def leftStep (p : List (Formula α) → List (Formula α) → Bool)
    (Γ Δ : List (Formula α)) : Formula α → Bool
  | atom _ => false
  | neg A => p (rest Γ (neg A)) (A :: Δ)
  | impl A B => p (rest Γ (impl A B)) (A :: Δ) && p (B :: rest Γ (impl A B)) Δ &&
      p (B :: rest Γ (impl A B)) (A :: Δ)
  | conj A B => p (A :: B :: rest Γ (conj A B)) Δ
  | disj A B => p (A :: rest Γ (disj A B)) Δ && p (B :: rest Γ (disj A B)) Δ &&
      p (A :: B :: rest Γ (disj A B)) Δ

/-- Try the right rule whose principal sentence is `φ`. -/
def rightStep (p : List (Formula α) → List (Formula α) → Bool)
    (Γ Δ : List (Formula α)) : Formula α → Bool
  | atom _ => false
  | neg A => p (A :: Γ) (rest Δ (neg A))
  | impl A B => p (A :: Γ) (B :: rest Δ (impl A B))
  | conj A B => p Γ (A :: rest Δ (conj A B)) && p Γ (B :: rest Δ (conj A B)) &&
      p Γ (A :: B :: rest Δ (conj A B))
  | disj A B => p Γ (A :: B :: rest Δ (disj A B))

/-- Root-first proof search with fuel. -/
def proveN (R : BaseRel α) : Nat → List (Formula α) → List (Formula α) → Bool
  | 0, _, _ => false
  | n + 1, Γ, Δ =>
    axiomCheck R Γ Δ || Γ.any (leftStep (proveN R n) Γ Δ) ||
      Δ.any (rightStep (proveN R n) Γ Δ)

/-- The decision procedure: fuel one above the connective count. -/
def prove (R : BaseRel α) (Γ Δ : List (Formula α)) : Bool :=
  proveN R (measure Γ Δ + 1) Γ Δ

/-- The axiom check is sound: each of pyNMMS's three axiom tests yields a
derivation (the first two by admissible Containment). -/
theorem axiomCheck_sound {R : BaseRel α} {Γ Δ : List (Formula α)}
    (h : axiomCheck R Γ Δ = true) : Derivable R Γ Δ := by
  simp only [axiomCheck, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
    List.contains_iff_mem] at h
  rcases h with (⟨φ, h1, _, h2⟩ | ⟨φ, h1, _, h2⟩) | ⟨⟨hg, hd⟩, hb⟩
  · exact overlap_derivable R φ h1 h2
  · exact overlap_derivable R φ h1 h2
  · exact Derivable.ax hg hd (Or.inr hb)

/-- **Soundness** of the search (any fuel). -/
theorem proveN_sound (R : BaseRel α) :
    ∀ n Γ Δ, proveN R n Γ Δ = true → Derivable R Γ Δ := by
  intro n
  induction n with
  | zero => intro Γ Δ h; simp [proveN] at h
  | succ n ih =>
    intro Γ Δ h
    simp only [proveN, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with (h | ⟨φ, hφ, h⟩) | ⟨φ, hφ, h⟩
    · exact axiomCheck_sound h
    · cases φ with
      | atom a => simp [leftStep] at h
      | neg A => simp only [leftStep] at h; exact Derivable.negL hφ (ih _ _ h)
      | impl A B =>
        simp only [leftStep, Bool.and_eq_true] at h
        exact Derivable.implL hφ (ih _ _ h.1.1) (ih _ _ h.1.2) (ih _ _ h.2)
      | conj A B => simp only [leftStep] at h; exact Derivable.conjL hφ (ih _ _ h)
      | disj A B =>
        simp only [leftStep, Bool.and_eq_true] at h
        exact Derivable.disjL hφ (ih _ _ h.1.1) (ih _ _ h.1.2) (ih _ _ h.2)
    · cases φ with
      | atom a => simp [rightStep] at h
      | neg A => simp only [rightStep] at h; exact Derivable.negR hφ (ih _ _ h)
      | impl A B => simp only [rightStep] at h; exact Derivable.implR hφ (ih _ _ h)
      | conj A B =>
        simp only [rightStep, Bool.and_eq_true] at h
        exact Derivable.conjR hφ (ih _ _ h.1.1) (ih _ _ h.1.2) (ih _ _ h.2)
      | disj A B => simp only [rightStep] at h; exact Derivable.disjR hφ (ih _ _ h)

/-- **Completeness** of the search: a derivable sequent is found with any fuel
above its connective count. -/
theorem proveN_complete {R : BaseRel α} {Γ Δ : List (Formula α)}
    (h : Derivable R Γ Δ) : ∀ n, measure Γ Δ < n → proveN R n Γ Δ = true := by
  induction h with
  | @ax Γ Δ hg hd hor =>
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
      simp only [proveN, Bool.or_eq_true]
      left; left
      simp only [axiomCheck, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
        List.contains_iff_mem]
      rcases hor with ⟨a, h1, h2⟩ | hb
      · left; right; exact ⟨atom a, h1, rfl, h2⟩
      · right; exact ⟨⟨hg, hd⟩, hb⟩
  | @negL Γ Δ A hm _ ih =>
    intro n hn; cases n with
    | zero => omega
    | succ n =>
      have hw := weight_rest hm
      simp only [proveN, Bool.or_eq_true, List.any_eq_true]
      left; right; exact ⟨_, hm, by simp only [leftStep]; exact ih n (by meas)⟩
  | @implL Γ Δ A B hm _ _ _ ih1 ih2 ih3 =>
    intro n hn; cases n with
    | zero => omega
    | succ n =>
      have hw := weight_rest hm
      simp only [proveN, Bool.or_eq_true, List.any_eq_true]
      left; right
      exact ⟨_, hm, by
        simp only [leftStep, Bool.and_eq_true]
        exact ⟨⟨ih1 n (by meas), ih2 n (by meas)⟩, ih3 n (by meas)⟩⟩
  | @conjL Γ Δ A B hm _ ih =>
    intro n hn; cases n with
    | zero => omega
    | succ n =>
      have hw := weight_rest hm
      simp only [proveN, Bool.or_eq_true, List.any_eq_true]
      left; right; exact ⟨_, hm, by simp only [leftStep]; exact ih n (by meas)⟩
  | @disjL Γ Δ A B hm _ _ _ ih1 ih2 ih3 =>
    intro n hn; cases n with
    | zero => omega
    | succ n =>
      have hw := weight_rest hm
      simp only [proveN, Bool.or_eq_true, List.any_eq_true]
      left; right
      exact ⟨_, hm, by
        simp only [leftStep, Bool.and_eq_true]
        exact ⟨⟨ih1 n (by meas), ih2 n (by meas)⟩, ih3 n (by meas)⟩⟩
  | @negR Γ Δ A hm _ ih =>
    intro n hn; cases n with
    | zero => omega
    | succ n =>
      have hw := weight_rest hm
      simp only [proveN, Bool.or_eq_true, List.any_eq_true]
      right; exact ⟨_, hm, by simp only [rightStep]; exact ih n (by meas)⟩
  | @implR Γ Δ A B hm _ ih =>
    intro n hn; cases n with
    | zero => omega
    | succ n =>
      have hw := weight_rest hm
      simp only [proveN, Bool.or_eq_true, List.any_eq_true]
      right; exact ⟨_, hm, by simp only [rightStep]; exact ih n (by meas)⟩
  | @conjR Γ Δ A B hm _ _ _ ih1 ih2 ih3 =>
    intro n hn; cases n with
    | zero => omega
    | succ n =>
      have hw := weight_rest hm
      simp only [proveN, Bool.or_eq_true, List.any_eq_true]
      right
      exact ⟨_, hm, by
        simp only [rightStep, Bool.and_eq_true]
        exact ⟨⟨ih1 n (by meas), ih2 n (by meas)⟩, ih3 n (by meas)⟩⟩
  | @disjR Γ Δ A B hm _ ih =>
    intro n hn; cases n with
    | zero => omega
    | succ n =>
      have hw := weight_rest hm
      simp only [proveN, Bool.or_eq_true, List.any_eq_true]
      right; exact ⟨_, hm, by simp only [rightStep]; exact ih n (by meas)⟩

/-- **The decision procedure is correct**: `prove` returns `true` exactly on
derivable sequents, for every base. -/
theorem prove_iff (R : BaseRel α) (Γ Δ : List (Formula α)) :
    prove R Γ Δ = true ↔ Derivable R Γ Δ :=
  ⟨proveN_sound R _ Γ Δ, fun h => proveN_complete h _ (by omega)⟩

/-- **Termination / depth bound.** Search depth never needs to exceed the
connective count: every fuel above it gives the same answer. -/
theorem proveN_stable (R : BaseRel α) (Γ Δ : List (Formula α)) (n : Nat)
    (hn : measure Γ Δ < n) : proveN R n Γ Δ = prove R Γ Δ := by
  cases h : prove R Γ Δ with
  | true => exact proveN_complete ((prove_iff R Γ Δ).mp h) n hn
  | false =>
    cases h' : proveN R n Γ Δ with
    | false => rfl
    | true =>
      have := proveN_complete (proveN_sound R n Γ Δ h') (measure Γ Δ + 1) (by omega)
      simp [prove] at h; rw [h] at this; exact absurd this (by simp)

/-- Decidability of NMMS derivability over any decidable base. -/
instance (R : BaseRel α) (Γ Δ : List (Formula α)) : Decidable (Derivable R Γ Δ) :=
  decidable_of_iff _ (prove_iff R Γ Δ)

end NMMS
