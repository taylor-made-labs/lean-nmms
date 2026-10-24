/-
  LeanNmms.Refute

  "Not derivable" certificates. A refutation is one failing branch: a list of
  steps, each naming a side, a principal sentence on that side, and which of
  its rule's premises to follow, ending at an atomic sequent that is not in
  the base. `refute` checks it in one pass, with no search. An accepted
  refutation is no longer than the connective count (`refute_length`).

  * `refute_sound`: a refutation that checks shows the sequent is not
    derivable, over every set-invariant base. Soundness needs invertibility:
    a derivable conclusion would make the chosen premise derivable too, down
    to the leaf.
  * `refute_complete`: every sequent that is not derivable has one, so
    `refute` accepts refutations for exactly the underivable sequents.
  * `findRefute` builds one (the search `nmms-lean` runs). What it returns
    is always a refutation that `refute` accepts (`findRefute_sound`), and on
    every underivable sequent it returns one (`findRefute_complete`).
  * `refuteOk_iff`: `nmms-lean`'s "refute_ok" (run `findRefute`, check its
    output with `refute`, `false` if it found nothing) is `true` exactly on
    the sequents that are not derivable, over every set-invariant base.

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

/-- An accepted refutation has at most as many steps as the sequent has
connectives: each step moves to a lighter premise. -/
theorem refute_length :
    ∀ (c : List (Step α)) (Γ Δ : List (Formula α)), refute R c Γ Δ = true →
      c.length ≤ measure Γ Δ
  | [], _, _, _ => by simp
  | s :: cs, Γ, Δ, h => by
    simp only [refute, Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨hm, h⟩ := h
    split at h
    · rename_i p hp
      have := premises_measure hm p (List.mem_of_getElem? hp)
      have := refute_length cs _ _ h
      simp only [List.length_cons]; omega
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

/-- Build a failing branch, with fuel one above the connective count. -/
def findRefute (R : BaseRel α) (Γ Δ : List (Formula α)) : Option (List (Step α)) :=
  findRefuteN R (measure Γ Δ + 1) Γ Δ

/-- Whatever `findRefuteN` returns is a refutation that `refute` accepts,
for every fuel and every base. -/
theorem findRefuteN_sound :
    ∀ n (Γ Δ : List (Formula α)) (c : List (Step α)), findRefuteN R n Γ Δ = some c →
      refute R c Γ Δ = true
  | 0, _, _, _, h => by simp [findRefuteN] at h
  | n + 1, Γ, Δ, c, h => by
    simp only [findRefuteN] at h
    split at h
    · rename_i hp
      obtain ⟨hg, hd⟩ := pickComplex_none hp
      cases hax : axiomCheck R Γ Δ
      · simp only [hax, Bool.false_eq_true, ite_false, Option.some.injEq] at h
        subst h
        simp only [axiomCheck, hg, hd, Bool.true_and] at hax
        simp [refute, hg, hd, hax]
      · simp [hax] at h
    · rename_i b φ hp
      obtain ⟨hm, _⟩ := pickComplex_some hp
      obtain ⟨⟨p, i⟩, hpi, hf⟩ := List.exists_of_findSome?_eq_some h
      obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hf
      have hi : (premises b φ Γ Δ)[i]? = some p := List.mem_zipIdx_iff_getElem?.mp hpi
      simp only [refute, Bool.and_eq_true, List.contains_iff_mem]
      exact ⟨hm, by rw [hi]; exact findRefuteN_sound n p.1 p.2 c' hc'⟩

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

/-- **`findRefute` is sound**: what it returns is a refutation that `refute`
accepts (over every base; over a set-invariant base that shows
non-derivability, `refute_sound`). -/
theorem findRefute_sound {Γ Δ : List (Formula α)} {c : List (Step α)}
    (h : findRefute R Γ Δ = some c) : refute R c Γ Δ = true :=
  findRefuteN_sound _ Γ Δ c h

/-- `findRefute` returns something on every underivable sequent. -/
theorem findRefute_isSome {Γ Δ : List (Formula α)}
    (h : ¬ Derivable R Γ Δ) : (findRefute R Γ Δ).isSome = true :=
  findRefuteN_complete _ Γ Δ (by omega) h

/-- **`findRefute` is complete**: on every underivable sequent it returns a
refutation that `refute` accepts. -/
theorem findRefute_complete {Γ Δ : List (Formula α)}
    (h : ¬ Derivable R Γ Δ) : ∃ c, findRefute R Γ Δ = some c ∧ refute R c Γ Δ = true := by
  cases hc : findRefute R Γ Δ with
  | none => have := findRefute_isSome (R := R) h; rw [hc] at this; cases this
  | some c => exact ⟨c, rfl, findRefute_sound hc⟩

/-- **What `nmms-lean` reports as "refute_ok"** (run `findRefute`, check its
output with `refute`, `false` if it found nothing) is `true` exactly on the
underivable sequents, over every set-invariant base. -/
theorem refuteOk_iff (hR : R.SetInvariant) (Γ Δ : List (Formula α)) :
    (match findRefute R Γ Δ with
      | some c => refute R c Γ Δ
      | none => false) = true ↔ ¬ Derivable R Γ Δ := by
  constructor
  · intro h
    split at h
    · exact refute_sound hR _ Γ Δ h
    · cases h
  · intro h
    obtain ⟨c, hc, hr⟩ := findRefute_complete h
    rw [hc]; exact hr

end NMMS
