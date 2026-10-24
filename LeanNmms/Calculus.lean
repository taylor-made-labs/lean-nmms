/-
  LeanNmms.Calculus

  The NMMS sequent calculus of Hlobil and Brandom (2025, ch. 3, pp. 108–111)
  over a supplied material base. `Derivable` is the specification: every
  other correctness result in the library is a theorem about it.

  * A sequent `Γ ⇒ Δ` has a finite *set* of sentences on each side. A side is
    a `List` read as a set: each rule's conclusion is stated up to `SetEq`,
    and `derivable_congr` proves that derivability depends only on the
    members of each side.
  * The base is any Boolean relation `R` on lists of atom names, read as sets
    (`BaseRel.SetInvariant`). pyNMMS's concrete base format is in
    `LeanNmms.Base`.
  * The axioms are exactly the atomic sequents in the base (Ax). Nothing else
    is an axiom. In particular Containment (a sentence on both sides) is *not*
    added: over a base without `p |~ p`, `p ⇒ p` is not derivable, and over
    the empty base nothing is (`emptyBase_underivable`). A base that obeys
    Containment is a hypothesis of the theorems that need it, never a
    default, in two forms: `BaseRel.Containment` for every atom of `α`, and
    `BaseRel.ContainmentOn L` for the atoms of a language `L` only. Adding
    the MONOTONE entries `a |~ a`, one per `a ∈ L` (`coEntries L`,
    `LeanNmms.Base`), gives any base the second. Over `String` or `Nat`
    atoms those entries alone never have the first, since `b ⇒ b` is
    missing for every atom `b ∉ L` (`baseRel_containment`). The second is
    what the theorems about sequents whose atoms are in `L` need.
  * The eight rules are the book's, including the third top sequents of L→,
    L∨ and R∧. In the book `Γ, A ⇒ Δ` is `Γ ∪ {A}`, so a rule's context may
    itself contain the principal sentence. Each constructor therefore takes
    the context `Γ₀` (or `Δ₀`) explicitly and only requires that the
    conclusion's side be `Γ₀ ∪ {principal}` as a set. The decision procedures
    always remove the principal sentence from the context; that this loses
    nothing is a theorem (`invertibility`, `LeanNmms.Invertibility`).
-/
import LeanNmms.Syntax

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- Two lists with the same members (the same finite set). -/
def SetEq {β : Type} (l l' : List β) : Prop := ∀ x, x ∈ l ↔ x ∈ l'

theorem SetEq.rfl' {β : Type} {l : List β} : SetEq l l := fun _ => Iff.rfl
theorem SetEq.symm {β : Type} {l l' : List β} (h : SetEq l l') : SetEq l' l :=
  fun x => (h x).symm
theorem SetEq.trans {β : Type} {a b c : List β} (h1 : SetEq a b) (h2 : SetEq b c) :
    SetEq a c := fun x => (h1 x).trans (h2 x)

theorem SetEq.cons {β : Type} {l l' : List β} (x : β) (h : SetEq l l') :
    SetEq (x :: l) (x :: l') := by
  intro y; simp [h y]

theorem SetEq.rest {l l' : List (Formula α)} (φ : Formula α) (h : SetEq l l') :
    SetEq (NMMS.rest l φ) (NMMS.rest l' φ) := by
  intro y; simp [h y]

theorem SetEq.atomsOf {l l' : List (Formula α)} (h : SetEq l l') :
    SetEq (NMMS.atomsOf l) (NMMS.atomsOf l') := by
  intro y; simp [h (atom y)]

/-- A member's side is the member together with the side minus every copy of
it: `l = {φ} ∪ (l ∖ {φ})`. -/
theorem setEq_cons_rest {φ : Formula α} {l : List (Formula α)} (h : φ ∈ l) :
    SetEq l (φ :: rest l φ) := by
  intro x; by_cases e : x = φ
  · subst e; simp [h]
  · simp [e]

/-- A member's side is the member together with the whole side:
`l = {φ} ∪ l` (the book's rule instance whose context keeps `φ`). -/
theorem setEq_cons_self {β : Type} {φ : β} {l : List β} (h : φ ∈ l) : SetEq l (φ :: l) := by
  intro x; by_cases e : x = φ
  · subst e; simp [h]
  · simp [e]

/-- A material base, abstractly: which atomic sequents (as lists of atom
names) it contains. NMMS takes its axioms from `R` and from nowhere else. -/
abbrev BaseRel (α : Type) := List α → List α → Bool

/-- A base relation that only looks at which atoms are on each side, i.e. a
relation on finite sets of atoms, as the book's base is. -/
def BaseRel.SetInvariant (R : BaseRel α) : Prop :=
  ∀ a b a' b', SetEq a a' → SetEq b b' → R a b = R a' b'

/-- The base obeys Containment: every atomic sequent whose sides share an atom
is in it. NMMS does not assume this; theorems that need it say so. This
quantifies over every atom of `α`, including atoms that no entry mentions, so
over `String` or `Nat` atoms the base `coEntries L` (`LeanNmms.Base`) never
has it; `ContainmentOn L` is the form it has. -/
def BaseRel.Containment (R : BaseRel α) : Prop :=
  ∀ X Y, (∃ a, a ∈ X ∧ a ∈ Y) → R X Y = true

/-- The base obeys Containment for the atoms of the language `L`: every
atomic sequent whose sides share an atom of `L` is in it. The MONOTONE
entries `a |~ a`, one per `a ∈ L`, supply exactly this
(`containmentOn_coEntries`, `LeanNmms.Base`). -/
def BaseRel.ContainmentOn (R : BaseRel α) (L : List α) : Prop :=
  ∀ X Y, (∃ a ∈ L, a ∈ X ∧ a ∈ Y) → R X Y = true

/-- Containment for every atom gives Containment for the atoms of any `L`. -/
theorem BaseRel.Containment.on {R : BaseRel α} (h : R.Containment) {L : List α} :
    R.ContainmentOn L :=
  fun X Y ⟨a, _, h1, h2⟩ => h X Y ⟨a, h1, h2⟩

/-- **NMMS derivability over the base `R`** (Hlobil and Brandom 2025, ch. 3):
`Derivable R Γ Δ` is `Γ ⇒ Δ`. In each rule `Γ₀` / `Δ₀` is the rule's
context, which may or may not contain the principal sentence. -/
inductive Derivable (R : BaseRel α) : List (Formula α) → List (Formula α) → Prop where
  /-- [Ax] `Γ ⇒ Δ` for sets of atoms `Γ`, `Δ` with `Γ |~ Δ` in the base. -/
  | ax {Γ Δ} : allAtomic Γ = true → allAtomic Δ = true → R (atomsOf Γ) (atomsOf Δ) = true →
      Derivable R Γ Δ
  /-- [L¬] Γ₀, ¬A ⇒ Δ  ⇐  Γ₀ ⇒ Δ, A -/
  | negL {Γ Γ₀ Δ A} : SetEq Γ (neg A :: Γ₀) →
      Derivable R Γ₀ (A :: Δ) → Derivable R Γ Δ
  /-- [L→] Γ₀, A→B ⇒ Δ  ⇐  Γ₀ ⇒ Δ, A;  Γ₀, B ⇒ Δ;  Γ₀, B ⇒ Δ, A -/
  | implL {Γ Γ₀ Δ A B} : SetEq Γ (impl A B :: Γ₀) →
      Derivable R Γ₀ (A :: Δ) → Derivable R (B :: Γ₀) Δ →
      Derivable R (B :: Γ₀) (A :: Δ) → Derivable R Γ Δ
  /-- [L∧] Γ₀, A∧B ⇒ Δ  ⇐  Γ₀, A, B ⇒ Δ -/
  | conjL {Γ Γ₀ Δ A B} : SetEq Γ (conj A B :: Γ₀) →
      Derivable R (A :: B :: Γ₀) Δ → Derivable R Γ Δ
  /-- [L∨] Γ₀, A∨B ⇒ Δ  ⇐  Γ₀, A ⇒ Δ;  Γ₀, B ⇒ Δ;  Γ₀, A, B ⇒ Δ -/
  | disjL {Γ Γ₀ Δ A B} : SetEq Γ (disj A B :: Γ₀) →
      Derivable R (A :: Γ₀) Δ → Derivable R (B :: Γ₀) Δ →
      Derivable R (A :: B :: Γ₀) Δ → Derivable R Γ Δ
  /-- [R¬] Γ ⇒ Δ₀, ¬A  ⇐  Γ, A ⇒ Δ₀ -/
  | negR {Γ Δ Δ₀ A} : SetEq Δ (neg A :: Δ₀) →
      Derivable R (A :: Γ) Δ₀ → Derivable R Γ Δ
  /-- [R→] Γ ⇒ Δ₀, A→B  ⇐  Γ, A ⇒ Δ₀, B -/
  | implR {Γ Δ Δ₀ A B} : SetEq Δ (impl A B :: Δ₀) →
      Derivable R (A :: Γ) (B :: Δ₀) → Derivable R Γ Δ
  /-- [R∧] Γ ⇒ Δ₀, A∧B  ⇐  Γ ⇒ Δ₀, A;  Γ ⇒ Δ₀, B;  Γ ⇒ Δ₀, A, B -/
  | conjR {Γ Δ Δ₀ A B} : SetEq Δ (conj A B :: Δ₀) →
      Derivable R Γ (A :: Δ₀) → Derivable R Γ (B :: Δ₀) →
      Derivable R Γ (A :: B :: Δ₀) → Derivable R Γ Δ
  /-- [R∨] Γ ⇒ Δ₀, A∨B  ⇐  Γ ⇒ Δ₀, A, B -/
  | disjR {Γ Δ Δ₀ A B} : SetEq Δ (disj A B :: Δ₀) →
      Derivable R Γ (A :: B :: Δ₀) → Derivable R Γ Δ

namespace Derivable

variable {R : BaseRel α} {Γ Δ : List (Formula α)} {A B : Formula α}

/-! Rule instances whose context is the side with the principal sentence
removed (`rest`), the form the decision procedures use. -/

theorem negL_rest (h : neg A ∈ Γ) (p : Derivable R (rest Γ (neg A)) (A :: Δ)) :
    Derivable R Γ Δ := negL (setEq_cons_rest h) p
theorem implL_rest (h : impl A B ∈ Γ) (p1 : Derivable R (rest Γ (impl A B)) (A :: Δ))
    (p2 : Derivable R (B :: rest Γ (impl A B)) Δ)
    (p3 : Derivable R (B :: rest Γ (impl A B)) (A :: Δ)) : Derivable R Γ Δ :=
  implL (setEq_cons_rest h) p1 p2 p3
theorem conjL_rest (h : conj A B ∈ Γ) (p : Derivable R (A :: B :: rest Γ (conj A B)) Δ) :
    Derivable R Γ Δ := conjL (setEq_cons_rest h) p
theorem disjL_rest (h : disj A B ∈ Γ) (p1 : Derivable R (A :: rest Γ (disj A B)) Δ)
    (p2 : Derivable R (B :: rest Γ (disj A B)) Δ)
    (p3 : Derivable R (A :: B :: rest Γ (disj A B)) Δ) : Derivable R Γ Δ :=
  disjL (setEq_cons_rest h) p1 p2 p3
theorem negR_rest (h : neg A ∈ Δ) (p : Derivable R (A :: Γ) (rest Δ (neg A))) :
    Derivable R Γ Δ := negR (setEq_cons_rest h) p
theorem implR_rest (h : impl A B ∈ Δ) (p : Derivable R (A :: Γ) (B :: rest Δ (impl A B))) :
    Derivable R Γ Δ := implR (setEq_cons_rest h) p
theorem conjR_rest (h : conj A B ∈ Δ) (p1 : Derivable R Γ (A :: rest Δ (conj A B)))
    (p2 : Derivable R Γ (B :: rest Δ (conj A B)))
    (p3 : Derivable R Γ (A :: B :: rest Δ (conj A B))) : Derivable R Γ Δ :=
  conjR (setEq_cons_rest h) p1 p2 p3
theorem disjR_rest (h : disj A B ∈ Δ) (p : Derivable R Γ (A :: B :: rest Δ (disj A B))) :
    Derivable R Γ Δ := disjR (setEq_cons_rest h) p

end Derivable

/-- **Sides are sets.** Derivability depends only on the members of each side,
provided the base does. -/
theorem derivable_congr {R : BaseRel α} (hR : R.SetInvariant)
    {Γ Δ : List (Formula α)} (h : Derivable R Γ Δ) :
    ∀ {Γ' Δ'}, SetEq Γ Γ' → SetEq Δ Δ' → Derivable R Γ' Δ' := by
  induction h with
  | ax hg hd hb =>
    intro Γ' Δ' e1 e2
    refine Derivable.ax ?_ ?_ ?_
    · rw [allAtomic_iff] at *; intro φ hφ; exact hg φ ((e1 φ).mpr hφ)
    · rw [allAtomic_iff] at *; intro φ hφ; exact hd φ ((e2 φ).mpr hφ)
    · rw [← hR _ _ _ _ e1.atomsOf e2.atomsOf]; exact hb
  | negL e _ ih =>
    intro Γ' Δ' e1 e2
    exact Derivable.negL (e1.symm.trans e) (ih SetEq.rfl' (e2.cons _))
  | implL e _ _ _ ih1 ih2 ih3 =>
    intro Γ' Δ' e1 e2
    exact Derivable.implL (e1.symm.trans e) (ih1 SetEq.rfl' (e2.cons _))
      (ih2 SetEq.rfl' e2) (ih3 SetEq.rfl' (e2.cons _))
  | conjL e _ ih =>
    intro Γ' Δ' e1 e2
    exact Derivable.conjL (e1.symm.trans e) (ih SetEq.rfl' e2)
  | disjL e _ _ _ ih1 ih2 ih3 =>
    intro Γ' Δ' e1 e2
    exact Derivable.disjL (e1.symm.trans e) (ih1 SetEq.rfl' e2) (ih2 SetEq.rfl' e2)
      (ih3 SetEq.rfl' e2)
  | negR e _ ih =>
    intro Γ' Δ' e1 e2
    exact Derivable.negR (e2.symm.trans e) (ih (e1.cons _) SetEq.rfl')
  | implR e _ ih =>
    intro Γ' Δ' e1 e2
    exact Derivable.implR (e2.symm.trans e) (ih (e1.cons _) SetEq.rfl')
  | conjR e _ _ _ ih1 ih2 ih3 =>
    intro Γ' Δ' e1 e2
    exact Derivable.conjR (e2.symm.trans e) (ih1 e1 SetEq.rfl') (ih2 e1 SetEq.rfl')
      (ih3 e1 SetEq.rfl')
  | disjR e _ ih =>
    intro Γ' Δ' e1 e2
    exact Derivable.disjR (e2.symm.trans e) (ih e1 SetEq.rfl')

theorem not_allAtomic_of_mem {φ : Formula α} {Γ Γ₀ : List (Formula α)}
    (e : SetEq Γ (φ :: Γ₀)) (hφ : φ.isAtom = false) : allAtomic Γ ≠ true := by
  intro h
  have := allAtomic_iff.mp h φ ((e φ).mpr (List.mem_cons_self ..))
  rw [hφ] at this; cases this

/-- An atomic sequent is derivable only as an axiom: no rule has an atomic
conclusion. -/
theorem derivable_atomic {R : BaseRel α} {Γ Δ : List (Formula α)} (hg : allAtomic Γ = true)
    (hd : allAtomic Δ = true) (h : Derivable R Γ Δ) : R (atomsOf Γ) (atomsOf Δ) = true := by
  cases h with
  | ax _ _ hb => exact hb
  | negL e _ => exact absurd hg (not_allAtomic_of_mem e rfl)
  | implL e _ _ _ => exact absurd hg (not_allAtomic_of_mem e rfl)
  | conjL e _ => exact absurd hg (not_allAtomic_of_mem e rfl)
  | disjL e _ _ _ => exact absurd hg (not_allAtomic_of_mem e rfl)
  | negR e _ => exact absurd hd (not_allAtomic_of_mem e rfl)
  | implR e _ => exact absurd hd (not_allAtomic_of_mem e rfl)
  | conjR e _ _ _ => exact absurd hd (not_allAtomic_of_mem e rfl)
  | disjR e _ => exact absurd hd (not_allAtomic_of_mem e rfl)

/-- **NMMS neither adds nor removes base consequences**: an atomic sequent is
derivable exactly when it is in the supplied base. -/
theorem derivable_atomic_iff {R : BaseRel α} {Γ Δ : List (Formula α)}
    (hg : allAtomic Γ = true) (hd : allAtomic Δ = true) :
    Derivable R Γ Δ ↔ R (atomsOf Γ) (atomsOf Δ) = true :=
  ⟨derivable_atomic hg hd, Derivable.ax hg hd⟩

/-- The empty base: no base consequences at all. -/
def emptyBase : BaseRel α := fun _ _ => false

/-- **Over the empty base nothing is derivable**, not even `p ⇒ p`: every
derivation needs axioms, and the axioms are the base's. -/
theorem emptyBase_underivable {Γ Δ : List (Formula α)} : ¬ Derivable emptyBase Γ Δ := by
  intro h
  induction h with
  | ax _ _ hb => simp [emptyBase] at hb
  | negL _ _ ih => exact ih
  | implL _ _ _ _ ih => exact ih
  | conjL _ _ ih => exact ih
  | disjL _ _ _ _ ih => exact ih
  | negR _ _ ih => exact ih
  | implR _ _ ih => exact ih
  | conjR _ _ _ _ ih => exact ih
  | disjR _ _ ih => exact ih

end NMMS
