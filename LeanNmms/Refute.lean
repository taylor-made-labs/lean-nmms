/-
  LeanNmms.Refute

  "Not derivable" certificates. A refutation is one failing branch: a list of
  steps, each naming a side, a principal sentence on that side, and which of
  its rule's premises to follow, ending at an atomic sequent that is not in
  the base. `refute` checks it in one pass, with no search. Its length is at
  most the connective count.

  * `refute_sound`: a refutation that checks shows the sequent is not
    derivable, over every set-invariant base. Soundness needs invertibility:
    a derivable conclusion would make the chosen premise derivable too, down
    to the leaf.
  * `refute_complete`: every sequent that is not derivable has one, so
    `refute` accepts refutations for exactly the underivable sequents.
  * `findRefute` builds it (the search `nmms-lean` runs);
    `findRefute_complete` proves it succeeds on every underivable sequent,
    and its output is in any case checked by `refute`.

  The leaf test is the base alone: an atomic sequent whose sides share an
  atom is a failing leaf unless the base contains it.
-/
import LeanNmms.Decide

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

variable {R : BaseRel α}

/-- One step of a failing branch: the side and principal sentence of a rule,
and which of its premises (0, 1 or 2) the branch follows. -/
structure Step (α : Type) where
  left : Bool
  φ : Formula α
  idx : Nat
  deriving Repr

/-- The refutation checker: follow the steps, recomputing each premise, and
require an atomic sequent outside the base at the end. -/
def refute (R : BaseRel α) : List (Step α) → List (Formula α) → List (Formula α) → Bool
  | [], Γ, Δ => allAtomic Γ && allAtomic Δ && !R (atomsOf Γ) (atomsOf Δ)
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
    rw [derivable_atomic hg hdd hd] at hn; cases hn
  | s :: cs, Γ, Δ, h, hd => by
    simp only [refute, Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨hm, h⟩ := h
    split at h
    · rename_i p hp
      exact refute_sound hR cs _ _ h (premises_inv hR hm hd p (List.mem_of_getElem? hp))
    · simp at h

/-- Some premise of a rule with an underivable conclusion is underivable. -/
theorem exists_underivable_premise {b : Bool} {φ : Formula α} {Γ Δ : List (Formula α)}
    (hm : φ ∈ side b Γ Δ) (hna : φ.isAtom = false) (hn : ¬ Derivable R Γ Δ) :
    ∃ (i : Nat) (p : List (Formula α) × List (Formula α)),
      (premises b φ Γ Δ)[i]? = some p ∧ ¬ Derivable R p.1 p.2 := by
  refine Classical.byContradiction fun hno => hn (premises_sound hm hna fun p hp => ?_)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  exact Classical.byContradiction fun hpd => hno ⟨i, p, hi, hpd⟩

/-- **Refutation completeness**: every sequent that is not derivable has a
refutation that checks. -/
theorem refute_complete :
    ∀ n (Γ Δ : List (Formula α)), measure Γ Δ < n → ¬ Derivable R Γ Δ →
      ∃ c, refute R c Γ Δ = true
  | 0, _, _, hn, _ => absurd hn (by omega)
  | n + 1, Γ, Δ, hn, hu => by
    cases hp : pickComplex Γ Δ with
    | none =>
      obtain ⟨hg, hd⟩ := pickComplex_none hp
      refine ⟨[], ?_⟩
      simp only [refute, hg, hd, Bool.true_and, Bool.not_eq_true']
      cases hb : R (atomsOf Γ) (atomsOf Δ)
      · rfl
      · exact absurd (Derivable.ax hg hd hb) hu
    | some bφ =>
      obtain ⟨b, φ⟩ := bφ
      obtain ⟨hm, hna⟩ := pickComplex_some hp
      obtain ⟨i, p, hi, hpu⟩ := exists_underivable_premise hm hna hu
      have hlt := premises_measure hm p (List.mem_of_getElem? hi)
      obtain ⟨c, hc⟩ := refute_complete n p.1 p.2 (by omega) hpu
      refine ⟨⟨b, φ, i⟩ :: c, ?_⟩
      simp only [refute, Bool.and_eq_true, List.contains_iff_mem]
      exact ⟨hm, by rw [hi]; exact hc⟩

/-- `refute` accepts a refutation exactly for the underivable sequents. -/
theorem refutable_iff (hR : R.SetInvariant) (Γ Δ : List (Formula α)) :
    (∃ c, refute R c Γ Δ = true) ↔ ¬ Derivable R Γ Δ :=
  ⟨fun ⟨c, hc⟩ => refute_sound hR c Γ Δ hc,
    fun h => refute_complete (measure Γ Δ + 1) Γ Δ (by omega) h⟩

/-- Build a failing branch. -/
def findRefuteN (R : BaseRel α) : Nat → List (Formula α) → List (Formula α) →
    Option (List (Step α))
  | 0, _, _ => none
  | n + 1, Γ, Δ =>
    match pickComplex Γ Δ with
    | none => if axiomCheck R Γ Δ then none else some []
    | some (b, φ) =>
      (premises b φ Γ Δ).zipIdx.findSome? (fun pi =>
        (findRefuteN R n pi.1.1 pi.1.2).map (fun c => ⟨b, φ, pi.2⟩ :: c))

def findRefute (R : BaseRel α) (Γ Δ : List (Formula α)) : Option (List (Step α)) :=
  findRefuteN R (measure Γ Δ + 1) Γ Δ

theorem findRefuteN_complete :
    ∀ n (Γ Δ : List (Formula α)), measure Γ Δ < n → ¬ Derivable R Γ Δ →
      (findRefuteN R n Γ Δ).isSome = true
  | 0, _, _, hn, _ => absurd hn (by omega)
  | n + 1, Γ, Δ, hn, hu => by
    simp only [findRefuteN]
    split
    · rename_i hp
      have hax : axiomCheck R Γ Δ = false :=
        Bool.eq_false_iff.mpr fun h => hu (axiomCheck_sound h)
      simp [hax]
    · rename_i b φ hp
      obtain ⟨hm, hna⟩ := pickComplex_some hp
      obtain ⟨i, p, hi, hpu⟩ := exists_underivable_premise hm hna hu
      have hlt := premises_measure hm p (List.mem_of_getElem? hi)
      have ih := findRefuteN_complete n p.1 p.2 (by omega) hpu
      rw [List.findSome?_isSome_iff]
      refine ⟨(p, i), List.mem_zipIdx_iff_getElem?.mpr hi, ?_⟩
      simpa using ih

/-- **`findRefute` finds a refutation for every underivable sequent.** -/
theorem findRefute_complete {Γ Δ : List (Formula α)}
    (h : ¬ Derivable R Γ Δ) : (findRefute R Γ Δ).isSome = true :=
  findRefuteN_complete _ Γ Δ (by omega) h

end NMMS
