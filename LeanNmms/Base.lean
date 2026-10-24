/-
  LeanNmms.Base

  pyNMMS's material base (`pynmms/base.py`, `pynmms/robustness.py`) as a
  `BaseRel`. A base is a finite list of entries `Γ₀ |~ Δ₀`, each with a
  robustness policy:

  * EXACT: matches only the atomic sequent `Γ₀ ⇒ Δ₀` itself (as sets).
  * MONOTONE: matches every `Γ ⇒ Δ` with `Γ₀ ⊆ Γ` and `Δ₀ ⊆ Δ`.
  * GUARDED: MONOTONE unless `Γ` meets `left`, `Δ` meets `right`, or for some
    exclusion pair `⟨x, y⟩`, `x ⊆ Γ` and `y ⊆ Δ`.

  pyNMMS normalises policies: it folds singleton exclusions into
  `left`/`right` and turns a GUARDED policy with no defeaters into MONOTONE.
  Neither changes which sequents match, so neither is modelled. pyNMMS also
  rejects an empty exclusion pair and defeaters on an EXACT or MONOTONE
  entry; `nmms-lean` refuses both when reading JSON, so the model never sees
  them (here an EXACT or MONOTONE entry has no defeaters at all).
  pyNMMS keeps one policy per pair (re-adding replaces it); the test harness
  sends Lean the base's own `to_dict()` serialisation, which has one entry per
  pair (`nmms-lean` refuses a base that lists a pair twice).

  `baseRel B` is the whole base: NMMS takes its axioms from it and from
  nowhere else. pyNMMS's `is_axiom` also accepts every atomic sequent whose
  sides share an atom ("Ax1", Containment); that is *not* part of `baseRel`
  or of the calculus. To give a base Containment, supply it for a language
  `L`: `coEntries L`, the MONOTONE entries `a |~ a`, one per `a ∈ L`,
  contributes exactly the atomic sequents whose sides share an atom of `L`
  (`baseRel_containment`), so `B ++ coEntries L` obeys Containment for the
  atoms of `L` whatever `B` is (`containmentOn_coEntries`). Over that base
  every classically valid sequent whose atoms are in `L` is derivable, and so
  is every sequent whose sides share a sentence over `L`
  (`supraclassical_coEntries`, `overlap_derivable_coEntries`,
  `LeanNmms.Classical`). Nothing is claimed for atoms outside `L`: in general
  that base need not obey `BaseRel.Containment`, which asks for every atom of
  `α`, and over `String` or `Nat` atoms `coEntries L` alone never does, since
  `b ⇒ b` is missing for every atom `b ∉ L` (`baseRel_containment`).
-/
import LeanNmms.Calculus

namespace NMMS

variable {α : Type} [DecidableEq α]

/-- Defeaters of a GUARDED entry. -/
structure Guard (α : Type) where
  left : List α := []
  right : List α := []
  pairs : List (List α × List α) := []
  deriving Repr

/-- pyNMMS's `Robustness` kinds. -/
inductive Robustness (α : Type) where
  | exact
  | monotone
  | guarded (g : Guard α)
  deriving Repr

/-- One base consequence `ant |~ con` with its policy. -/
structure Entry (α : Type) where
  ant : List α
  con : List α
  rob : Robustness α := .exact
  deriving Repr

/-- `x ⊆ y`, as pyNMMS's `all(a in y for a in x)`. -/
def subsetB (x y : List α) : Bool := x.all (fun a => y.contains a)

/-- Set equality (pyNMMS's same-size-then-subset test on sets). -/
def setEqB (x y : List α) : Bool := subsetB x y && subsetB y x

/-- pyNMMS's `Robustness.allows` for a GUARDED entry. -/
def Guard.allows (g : Guard α) (Γa Δa : List α) : Bool :=
  !(g.left.any (fun a => Γa.contains a)) && !(g.right.any (fun a => Δa.contains a)) &&
  !(g.pairs.any (fun p => subsetB p.1 Γa && subsetB p.2 Δa))

/-- Does this entry license the atomic sequent `Γa ⇒ Δa`? -/
def Entry.matches (e : Entry α) (Γa Δa : List α) : Bool :=
  match e.rob with
  | .exact => setEqB e.ant Γa && setEqB e.con Δa
  | .monotone => subsetB e.ant Γa && subsetB e.con Δa
  | .guarded g => subsetB e.ant Γa && subsetB e.con Δa && g.allows Γa Δa

/-- The base relation of a list of entries: pyNMMS's `MaterialBase.is_axiom`
"Ax2" (its "Ax1", Containment, is not included). -/
def baseRel (B : List (Entry α)) : BaseRel α :=
  fun Γa Δa => B.any (fun e => e.matches Γa Δa)

theorem contains_congr {l l' : List α} (h : SetEq l l') (a : α) :
    l.contains a = l'.contains a := by
  rw [Bool.eq_iff_iff]; simp [h a]

theorem all_congr' {β : Type} {l l' : List β} (h : SetEq l l') (f : β → Bool) :
    l.all f = l'.all f := by
  rw [Bool.eq_iff_iff]; simp [List.all_eq_true, h _]

theorem subsetB_congr {x x' y y' : List α} (hx : SetEq x x') (hy : SetEq y y') :
    subsetB x y = subsetB x' y' := by
  unfold subsetB
  rw [all_congr' hx]
  congr 1; funext a; exact contains_congr hy a

/-- pyNMMS's base only looks at which atoms are on each side. -/
theorem baseRel_setInvariant (B : List (Entry α)) : (baseRel B).SetInvariant := by
  intro a b a' b' ha hb
  unfold baseRel
  congr 1; funext e
  have r : SetEq e.ant e.ant := fun _ => Iff.rfl
  have s : SetEq e.con e.con := fun _ => Iff.rfl
  unfold Entry.matches
  split
  · simp only [setEqB, subsetB_congr r ha, subsetB_congr ha r, subsetB_congr s hb,
      subsetB_congr hb s]
  · simp only [subsetB_congr r ha, subsetB_congr s hb]
  · rename_i g _
    simp only [Guard.allows, subsetB_congr r ha, subsetB_congr s hb]
    have e1 : (g.left.any fun x => a.contains x) = (g.left.any fun x => a'.contains x) := by
      congr 1; funext x; exact contains_congr ha x
    have e2 : (g.right.any fun x => b.contains x) = (g.right.any fun x => b'.contains x) := by
      congr 1; funext x; exact contains_congr hb x
    have e3 : (g.pairs.any fun p => subsetB p.1 a && subsetB p.2 b) =
        (g.pairs.any fun p => subsetB p.1 a' && subsetB p.2 b') := by
      congr 1; funext p
      have r1 : SetEq p.1 p.1 := fun _ => Iff.rfl
      have r2 : SetEq p.2 p.2 := fun _ => Iff.rfl
      rw [subsetB_congr r1 ha, subsetB_congr r2 hb]
    rw [e1, e2, e3]

/-- Containment for the atoms of `L`, as pyNMMS entries: a MONOTONE `a |~ a`
for each `a ∈ L`. -/
def coEntries (L : List α) : List (Entry α) :=
  L.map fun a => { ant := [a], con := [a], rob := .monotone }

/-- The base of two lists of entries contains what either contains. -/
theorem baseRel_append (B B' : List (Entry α)) (X Y : List α) :
    baseRel (B ++ B') X Y = (baseRel B X Y || baseRel B' X Y) := by
  simp [baseRel, List.any_append]

/-- MONOTONE `a |~ a` entries, one per atom of `L`, supply Containment for
the atoms of `L` and nothing else. -/
theorem baseRel_containment (L : List α) (X Y : List α) :
    baseRel (coEntries L) X Y = true ↔ ∃ a ∈ L, a ∈ X ∧ a ∈ Y := by
  simp [coEntries, baseRel, Entry.matches, subsetB]

/-- **Containment for `L`, supplied in the base**: any base `B` with the
entries `coEntries L` added obeys Containment for the atoms of `L`. -/
theorem containmentOn_coEntries (B : List (Entry α)) (L : List α) :
    (baseRel (B ++ coEntries L)).ContainmentOn L := by
  intro X Y h
  rw [baseRel_append, Bool.or_eq_true]
  exact Or.inr ((baseRel_containment L X Y).mpr h)

/-- Hence, over a pyNMMS base, NMMS derivability depends only on the sets. -/
theorem derivable_congr_base (B : List (Entry α)) {Γ Δ Γ' Δ' : List (Formula α)}
    (h : Derivable (baseRel B) Γ Δ) (e1 : SetEq Γ Γ') (e2 : SetEq Δ Δ') :
    Derivable (baseRel B) Γ' Δ' :=
  derivable_congr (baseRel_setInvariant B) h e1 e2

end NMMS
