/-
  LeanNmms.Derivation

  Certifying a whole chain of material inferences from initial premises, not
  only its last step (fix 2 of the 21 Oct 2026 adversarial review).

  **This is not NMMS derivability.** NMMS has no Cut: `p ⇒ q` and `q ⇒ r`
  being derivable does not make `p ⇒ r` derivable. `Closure` chains
  single-conclusion NMMS steps, so membership of a claim in it is a further
  calculation on top of NMMS, and `nmms-lean` reports it as `"in_closure"`,
  never as `"derivable"`. Each *step* is NMMS-derivable over the base (checked
  by the proved certificate checker); the chain is not a sequent derivation.

  **The closure.** `Closure B Γ₀ φ` is the least set of sentences that
  contains `Γ₀` and is closed under single-conclusion NMMS steps: if every
  member of some list `P` is in the set and `P ⇒ φ` is derivable over the base
  `B` (pyNMMS's `MaterialBase`, `LeanNmms.Base`), then `φ` is in the set.
  `P` may be any list of members, a proper subset included, so EXACT base
  entries chain. Because steps may draw on any subset, this closure is
  *monotone* in `Γ₀`: a GUARDED entry's defeater that is in `Γ₀` does not
  block a step whose premises leave the defeater out. It therefore contains
  every atom that the iteration "add each atom derivable from everything
  reached so far" (pyNMMS's whole-set reading) reaches, and may contain more.

  **"Follows" certificates.** An ordered derivation is a list of steps, each
  naming its premises, its conclusion and a local proof tree (`Cert`,
  `LeanNmms.Certificate`). `checkDerivation` checks every step in order:
  each premise must already be available (in `Γ₀` or concluded by an earlier
  step), and the local tree must check `premises ⇒ [conclusion]` with the
  proved checker `check`. A step can never cite its own or a later
  conclusion. `checkDerivation_sound`: an accepted derivation puts the claim
  in `Closure B Γ₀`.

  **"Refuted" certificates.** For atomic `Γ₀` and an atomic claim, a closure
  refutation lists ordered steps and the complete set `A` of atoms they
  reach. `checkRefutation` checks the steps (so every atom of `A` is in the
  closure), that `Γ₀ ⊆ A`, that the claim is not in `A`, and *saturation*:
  no base entry fires on a pair `(X, Y)` with `X ⊆ A` and `Y` disjoint from
  `A` (checked entry by entry: EXACT, MONOTONE and GUARDED matching is
  antitone beyond the entry's own antecedent and consequent).
  `checkRefutation_sound`: then the claim is **not** in `Closure B Γ₀`.
  The proof reads `A` as a classical valuation (`a` true iff `a ∈ A`): given
  saturation every base axiom is true under it, and every NMMS rule preserves
  truth under one valuation (`valuation_sound`, `LeanNmms.Classical`), so the
  whole closure is true and the claim, false, is outside it. The check is conservative: an entry that concludes nothing (an
  exclusion) with a reached antecedent, or one with several consequents none
  of them reached, fails saturation even where the claim may in fact be
  outside the closure; such cases are rejected, never certified.
-/
import LeanNmms.Certificate
import LeanNmms.Classical
import LeanNmms.Base

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- One step of an ordered derivation: `premises ⇒ [conclusion]`, with its
local proof tree. -/
structure DerivationStep (α : Type) where
  premises : List (Formula α)
  conclusion : Formula α
  cert : Cert α
  deriving Repr

/-- The closure of `initial` under single-conclusion NMMS steps over the
base `B`, from any list of members (see the module header). -/
inductive Closure (B : List (Entry α)) (initial : List (Formula α)) : Formula α → Prop where
  | init {φ : Formula α} : φ ∈ initial → Closure B initial φ
  | step {P : List (Formula α)} {φ : Formula α} :
      (∀ p ∈ P, Closure B initial p) → Derivable (baseRel B) P [φ] → Closure B initial φ

/-- Check the steps in order from the sentences `avail`; on success return
everything available afterwards (the step conclusions in front). -/
def checkSteps (B : List (Entry α)) :
    List (Formula α) → List (DerivationStep α) → Option (List (Formula α))
  | avail, [] => some avail
  | avail, s :: rest =>
    if s.premises.all (fun p => avail.contains p) &&
        check (baseRel B) s.cert s.premises [s.conclusion] then
      checkSteps B (s.conclusion :: avail) rest
    else none

/-- The ordered-derivation checker: every step checks, and the claim is
available at the end. -/
def checkDerivation (B : List (Entry α)) (initial : List (Formula α))
    (steps : List (DerivationStep α)) (claim : Formula α) : Bool :=
  match checkSteps B initial steps with
  | some avail => avail.contains claim
  | none => false

theorem checkSteps_sound (B : List (Entry α)) (initial : List (Formula α)) :
    ∀ (steps : List (DerivationStep α)) (avail out : List (Formula α)),
      (∀ φ ∈ avail, Closure B initial φ) → checkSteps B avail steps = some out →
      ∀ φ ∈ out, Closure B initial φ
  | [], avail, out, h, e => by
    simp only [checkSteps, Option.some.injEq] at e
    subst e; exact h
  | s :: rest, avail, out, h, e => by
    simp only [checkSteps] at e
    split at e
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hc
      obtain ⟨hp, hk⟩ := hc
      have hs : Closure B initial s.conclusion :=
        Closure.step (fun p hp' => h p (hp p hp')) (check_sound _ _ _ _ hk)
      refine checkSteps_sound B initial rest _ out ?_ e
      intro φ hφ
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact hs
      · exact h φ hφ
    · simp at e

/-- **Ordered-derivation soundness**: an accepted derivation puts the claim in
the closure of the initial premises. -/
theorem checkDerivation_sound {B : List (Entry α)} {initial : List (Formula α)}
    {steps : List (DerivationStep α)} {claim : Formula α}
    (h : checkDerivation B initial steps claim = true) : Closure B initial claim := by
  unfold checkDerivation at h
  split at h
  · rename_i out e
    exact checkSteps_sound B initial steps initial out (fun φ hφ => Closure.init hφ) e
      claim (List.contains_iff_mem.mp h)
  · simp at h

/-! ### Closure refutations -/

/-- A "not in the closure" certificate: ordered steps and the complete set of
atoms they reach. -/
structure ClosureRefutation (α : Type) where
  steps : List (DerivationStep α)
  closure : List α
  deriving Repr

/-- Does entry `e` license some atomic sequent `X ⇒ Y` with `X ⊆ A` and `Y`
disjoint from `A`? Matching is antitone beyond the entry's own antecedent
and consequent, so the entry's own pair is the test. -/
def Entry.firesOn (e : Entry α) (A : List α) : Bool :=
  subsetB e.ant A && e.con.all (fun y => !A.contains y) &&
  match e.rob with
  | .exact => true
  | .monotone => true
  | .guarded g => g.allows e.ant e.con

/-- The closure-refutation checker (see the module header). -/
def checkRefutation (B : List (Entry α)) (initial : List (Formula α))
    (cert : ClosureRefutation α) (claim : Formula α) : Bool :=
  match claim with
  | atom c =>
    allAtomic initial && (atomsOf initial).all (fun a => cert.closure.contains a) &&
    !cert.closure.contains c && B.all (fun e => !e.firesOn cert.closure) &&
    match checkSteps B initial cert.steps with
    | some avail => cert.closure.all (fun a => avail.contains (atom a))
    | none => false
  | _ => false

theorem subsetB_true {x y : List α} : subsetB x y = true ↔ ∀ a ∈ x, a ∈ y := by
  simp [subsetB]

/-- A guard that allows a pair allows every smaller pair. -/
theorem Guard.allows_anti (g : Guard α) {X Y X' Y' : List α}
    (hx : ∀ a ∈ X', a ∈ X) (hy : ∀ a ∈ Y', a ∈ Y) (h : g.allows X Y = true) :
    g.allows X' Y' = true := by
  simp only [Guard.allows, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
    List.contains_iff_mem] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨fun a ha hX => h1 a ha (hx a hX), fun a ha hY => h2 a ha (hy a hY)⟩, ?_⟩
  intro p hp hc
  apply h3 p hp
  rw [subsetB_true, subsetB_true] at hc ⊢
  exact ⟨fun a ha => hx a (hc.1 a ha), fun a ha => hy a (hc.2 a ha)⟩

/-- Saturation makes the base true under the valuation "`a` is in `A`". -/
theorem base_true_of_saturated {B : List (Entry α)} {A : List α}
    (hs : B.all (fun e => !e.firesOn A) = true) :
    ∀ X Y, baseRel B X Y = true → (∀ x ∈ X, A.contains x = true) →
      ∃ y ∈ Y, A.contains y = true := by
  intro X Y hb hX
  refine Classical.byContradiction fun hno => ?_
  have hY : ∀ y ∈ Y, y ∉ A := by
    intro y hy hyA; exact hno ⟨y, hy, List.contains_iff_mem.mpr hyA⟩
  simp only [baseRel, List.any_eq_true] at hb
  obtain ⟨e, he, hm⟩ := hb
  have hnf := List.all_eq_true.mp hs e he
  simp only [Bool.not_eq_true'] at hnf
  have hXA : ∀ x ∈ X, x ∈ A := fun x hx => List.contains_iff_mem.mp (hX x hx)
  unfold Entry.matches at hm
  unfold Entry.firesOn at hnf
  split at hm <;> rename_i hr <;> simp only [hr] at hnf
  · -- exact
    simp only [setEqB, Bool.and_eq_true, subsetB_true] at hm
    obtain ⟨⟨ha1, _⟩, ⟨hc1, _⟩⟩ := hm
    simp only [Bool.and_true, Bool.and_eq_false_iff, subsetB, List.all_eq_false,
      List.contains_iff_mem, Bool.not_eq_true', Bool.not_eq_false] at hnf
    rcases hnf with ⟨a, ha, hn⟩ | ⟨y, hy, hyA⟩
    · exact hn (hXA a (ha1 a ha))
    · exact hY y (hc1 y hy) hyA
  · -- monotone
    simp only [Bool.and_eq_true, subsetB_true] at hm
    obtain ⟨ha1, hc1⟩ := hm
    simp only [Bool.and_true, Bool.and_eq_false_iff, subsetB, List.all_eq_false,
      List.contains_iff_mem, Bool.not_eq_true', Bool.not_eq_false] at hnf
    rcases hnf with ⟨a, ha, hn⟩ | ⟨y, hy, hyA⟩
    · exact hn (hXA a (ha1 a ha))
    · exact hY y (hc1 y hy) hyA
  · -- guarded
    rename_i g
    simp only [Bool.and_eq_true, subsetB_true] at hm
    obtain ⟨⟨ha1, hc1⟩, hg⟩ := hm
    have hg' := Guard.allows_anti g ha1 hc1 hg
    simp only [hg', Bool.and_true, Bool.and_eq_false_iff, subsetB, List.all_eq_false,
      List.contains_iff_mem, Bool.not_eq_true', Bool.not_eq_false] at hnf
    rcases hnf with ⟨a, ha, hn⟩ | ⟨y, hy, hyA⟩
    · exact hn (hXA a (ha1 a ha))
    · exact hY y (hc1 y hy) hyA

/-- **Closure-refutation soundness**: an accepted refutation shows the claim
is not in the closure of the initial premises, and every atom it lists is. -/
theorem checkRefutation_sound {B : List (Entry α)} {initial : List (Formula α)}
    {cert : ClosureRefutation α} {claim : Formula α}
    (h : checkRefutation B initial cert claim = true) :
    ¬ Closure B initial claim ∧ ∀ a ∈ cert.closure, Closure B initial (atom a) := by
  unfold checkRefutation at h
  split at h
  · rename_i c
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨hat, hinit⟩, hc⟩, hs⟩, hsteps⟩ := h
    simp only [List.all_eq_true, List.contains_iff_mem] at hinit
    let v : α → Bool := fun a => cert.closure.contains a
    have hR := base_true_of_saturated hs
    have htrue : ∀ φ, Closure B initial φ → φ.eval v = true := by
      intro φ hφ
      induction hφ with
      | init hm =>
        rename_i ψ
        obtain ⟨a, rfl⟩ := isAtom_iff.mp (allAtomic_iff.mp hat _ hm)
        simp only [Formula.eval, v]
        exact List.contains_iff_mem.mpr (hinit a (mem_atomsOf.mpr hm))
      | step _ hd ih =>
        obtain ⟨ψ, hψ, ht⟩ := valuation_sound v hR hd ih
        simp only [List.mem_singleton] at hψ
        subst hψ; exact ht
    refine ⟨fun hcl => ?_, ?_⟩
    · have := htrue _ hcl
      simp only [Formula.eval, v] at this
      rw [this] at hc; cases hc
    · split at hsteps
      · rename_i out e
        intro a ha
        have := checkSteps_sound B initial cert.steps initial out
          (fun φ hφ => Closure.init hφ) e (atom a)
        simp only [List.all_eq_true, List.contains_iff_mem] at hsteps
        exact this (hsteps a ha)
      · simp at hsteps
  · simp at h

end NMMS
