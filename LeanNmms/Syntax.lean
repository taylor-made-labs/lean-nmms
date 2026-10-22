/-
  LeanNmms.Syntax

  The propositional language of NMMS as pyNMMS 0.15.1 implements it
  (`pynmms/syntax.py`): atoms, negation, conjunction, disjunction, implication.

  Design notes.
  * Atoms are a type parameter `α` with decidable equality. The executable uses
    `String` (pyNMMS atom names); the proofs and the small worked examples use
    `Nat`, so that `decide` can evaluate them in the kernel.
  * A sequent side is a `List`, read as a set: everything the calculus and the
    decision procedure look at is membership, never position or multiplicity.
    `LeanNmms.Calculus.derivable_congr` proves that derivability only depends on
    membership, which is how pyNMMS's `frozenset` sides are modelled.
  * `rest l φ` removes every copy of `φ` from `l`. It is pyNMMS's
    `Sequent.without_left` / `without_right` (set difference with `{φ}`).
-/

namespace NMMS

/-- Propositional sentences. Mirrors pyNMMS's `Sentence` AST (`type` in
`atom | neg | conj | disj | impl`). -/
inductive Formula (α : Type) where
  | atom : α → Formula α
  | neg : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
  | impl : Formula α → Formula α → Formula α
  deriving DecidableEq, Repr, Inhabited

namespace Formula

variable {α : Type}

/-- Number of connective occurrences (pyNMMS `connective_count`). -/
def conn : Formula α → Nat
  | atom _ => 0
  | neg a => a.conn + 1
  | conj a b => a.conn + b.conn + 1
  | disj a b => a.conn + b.conn + 1
  | impl a b => a.conn + b.conn + 1

/-- True exactly for atoms (pyNMMS's atom/complex partition of a side). -/
def isAtom : Formula α → Bool
  | atom _ => true
  | _ => false

theorem ne_neg (a : Formula α) : a ≠ neg a := by
  intro h; have := congrArg conn h; simp [conn] at this
theorem ne_conj_l (a b : Formula α) : a ≠ conj a b := by
  intro h; have := congrArg conn h; simp [conn] at this; omega
theorem ne_conj_r (a b : Formula α) : b ≠ conj a b := by
  intro h; have := congrArg conn h; simp [conn] at this; omega
theorem ne_disj_l (a b : Formula α) : a ≠ disj a b := by
  intro h; have := congrArg conn h; simp [conn] at this; omega
theorem ne_disj_r (a b : Formula α) : b ≠ disj a b := by
  intro h; have := congrArg conn h; simp [conn] at this; omega
theorem ne_impl_l (a b : Formula α) : a ≠ impl a b := by
  intro h; have := congrArg conn h; simp [conn] at this; omega
theorem ne_impl_r (a b : Formula α) : b ≠ impl a b := by
  intro h; have := congrArg conn h; simp [conn] at this; omega

end Formula

open Formula

variable {α : Type} [DecidableEq α]

/-- Total connective count of a side, counting repeated entries. This is the
termination measure: every rule premise has a strictly smaller total. -/
def weight : List (Formula α) → Nat
  | [] => 0
  | φ :: l => φ.conn + weight l

/-- The side with every copy of `φ` removed (set difference). -/
def rest (l : List (Formula α)) (φ : Formula α) : List (Formula α) :=
  l.filter (fun x => x != φ)

/-- The atom names occurring on a side (what pyNMMS hands to
`MaterialBase.is_axiom`). -/
def atomsOf : List (Formula α) → List α
  | [] => []
  | atom a :: l => a :: atomsOf l
  | _ :: l => atomsOf l

/-- Every entry of the side is an atom. -/
def allAtomic (l : List (Formula α)) : Bool := l.all Formula.isAtom

@[simp] theorem weight_nil : weight ([] : List (Formula α)) = 0 := rfl
@[simp] theorem weight_cons (φ : Formula α) (l) : weight (φ :: l) = φ.conn + weight l := rfl

@[simp] theorem mem_rest {x φ : Formula α} {l : List (Formula α)} :
    x ∈ rest l φ ↔ x ∈ l ∧ x ≠ φ := by
  simp [rest]

theorem weight_rest_le (l : List (Formula α)) (φ : Formula α) :
    weight (rest l φ) ≤ weight l := by
  induction l with
  | nil => simp [rest]
  | cons x l ih =>
    by_cases h : x = φ
    · subst h; simp [rest] at *; omega
    · simp [rest, h] at *; omega

/-- Removing a member `φ` lowers the weight by at least `φ.conn`. -/
theorem weight_rest {l : List (Formula α)} {φ : Formula α} (h : φ ∈ l) :
    weight (rest l φ) + φ.conn ≤ weight l := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    by_cases hx : x = φ
    · subst hx
      have := weight_rest_le l x
      simp [rest] at *; omega
    · have h' : φ ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      have := ih h'
      simp [rest, hx] at *; omega

@[simp] theorem mem_atomsOf {a : α} {l : List (Formula α)} :
    a ∈ atomsOf l ↔ atom a ∈ l := by
  induction l with
  | nil => simp [atomsOf]
  | cons x l ih =>
    cases x <;> simp [atomsOf, ih]

theorem allAtomic_iff {l : List (Formula α)} :
    allAtomic l = true ↔ ∀ φ ∈ l, φ.isAtom = true := by
  simp [allAtomic]

theorem isAtom_iff {φ : Formula α} : φ.isAtom = true ↔ ∃ a, φ = atom a := by
  cases φ <;> simp [Formula.isAtom]

end NMMS
