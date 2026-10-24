/- Kernel examples for the NMMS rules of Hlobil and Brandom (2025, ch. 3,
   pp. 108–111): the axioms are the supplied base and nothing else, each rule
   (with its third premise where it has one), sides as sets, and the book's
   rule instances whose context keeps the principal sentence. Every verdict
   below is evaluated by the kernel (`decide`) through `fastProve`, which
   `fastProve_iff` proves equal to `Derivable`. Atoms: p = 0, q = 1, r = 2. -/
import LeanNmms

open NMMS Formula

namespace NmmsRulesTests

abbrev p : Formula Nat := atom 0
abbrev q : Formula Nat := atom 1
abbrev r : Formula Nat := atom 2

def ent (ant con : List Nat) (rob : Robustness Nat := .exact) : Entry Nat :=
  { ant, con, rob }

/-- The base `{p |~ q}`. -/
def pq : List (Entry Nat) := [ent [0] [1]]
/-- The base with nothing in it. -/
def empty : List (Entry Nat) := []
/-- Containment for p, q, r, supplied explicitly. -/
def co : List (Entry Nat) := [ent [0] [0] .monotone, ent [1] [1] .monotone, ent [2] [2] .monotone]

/-! ### The known error: Containment is not added -/

example : ¬ Derivable (baseRel empty) [p] [p] := by decide
example : ¬ Derivable (emptyBase : BaseRel Nat) [p] [p] := emptyBase_underivable
example : ¬ Derivable (baseRel empty) [neg p] [neg p] := by decide
example : ¬ Derivable (baseRel empty) [conj p q] [p] := by decide
example : ¬ Derivable (baseRel empty) [] [impl p p] := by decide
example : ¬ Derivable (baseRel empty) [] [disj p (neg p)] := by decide
example : ¬ Derivable (baseRel pq) [p] [p] := by decide
example : ¬ Derivable (baseRel pq) [p, q] [q] := by decide
-- The axiom check never accepts a shared sentence on its own.
example : axiomCheck (baseRel empty) [p] [p] = false := by decide
example : check (baseRel empty) .ax [conj p q] [conj p q] = false := by decide

/-! ### Ax: exactly the base's atomic sequents -/

example : Derivable (baseRel pq) [p] [q] := by decide
example : ¬ Derivable (baseRel pq) [q] [p] := by decide
example : ¬ Derivable (baseRel pq) [p, r] [q] := by decide
example : ¬ Derivable (baseRel pq) [p] [q, r] := by decide
-- sides are sets: repetition and order do not matter
example : Derivable (baseRel pq) [p, p] [q, q] := by decide

/-! ### Single-premise rules -/

-- L¬: p, ¬q ⇒  from  p ⇒ q
example : Derivable (baseRel pq) [p, neg q] [] := by decide
-- R¬: ⇒ ¬p, q  from  p ⇒ q
example : Derivable (baseRel pq) [] [neg p, q] := by decide
-- R→: ⇒ p → q  from  p ⇒ q
example : Derivable (baseRel pq) [] [impl p q] := by decide
example : ¬ Derivable (baseRel pq) [] [impl q p] := by decide
-- L∧: p ∧ p ⇒ q  from  p, p ⇒ q, which is p ⇒ q
example : Derivable (baseRel pq) [conj p p] [q] := by decide
example : ¬ Derivable (baseRel pq) [conj p r] [q] := by decide
-- R∨: p ⇒ q ∨ q  from  p ⇒ q, q
example : Derivable (baseRel pq) [p] [disj q q] := by decide
example : ¬ Derivable (baseRel pq) [p] [disj q r] := by decide

/-! ### Three-premise rules: every premise is needed, the third included -/

-- R∧: ⇒ p ∧ q  from  ⇒ p;  ⇒ q;  ⇒ p, q
def rconj : List (Entry Nat) := [ent [] [0], ent [] [1]]
example : ¬ Derivable (baseRel rconj) [] [conj p q] := by decide
example : Derivable (baseRel (ent [] [0, 1] :: rconj)) [] [conj p q] := by decide
example : ¬ Derivable (baseRel [ent [] [0], ent [] [0, 1]]) [] [conj p q] := by decide

-- L∨: p ∨ q ⇒  from  p ⇒;  q ⇒;  p, q ⇒
def ldisj : List (Entry Nat) := [ent [0] [], ent [1] []]
example : ¬ Derivable (baseRel ldisj) [disj p q] [] := by decide
example : Derivable (baseRel (ent [0, 1] [] :: ldisj)) [disj p q] [] := by decide
example : ¬ Derivable (baseRel [ent [0] [], ent [0, 1] []]) [disj p q] [] := by decide

-- L→: p → q ⇒  from  ⇒ p;  q ⇒;  q ⇒ p
def limpl : List (Entry Nat) := [ent [] [0], ent [1] []]
example : ¬ Derivable (baseRel limpl) [impl p q] [] := by decide
example : Derivable (baseRel (ent [1] [0] :: limpl)) [impl p q] [] := by decide
example : ¬ Derivable (baseRel [ent [] [0], ent [1] [0]]) [impl p q] [] := by decide

/-! ### With Containment supplied in the base, classical reasoning returns -/

example : Derivable (baseRel co) [p] [p] := by decide
example : Derivable (baseRel co) [conj p q] [p] := by decide
example : Derivable (baseRel co) [] [disj p (neg p)] := by decide
example : Derivable (baseRel co) [impl p q, p] [q] := by decide
example : ¬ Derivable (baseRel co) [disj p q] [p] := by decide
example (Γ Δ : List (Formula Nat)) : Derivable containmentBase Γ Δ ↔ Valid Γ Δ :=
  containmentBase_iff_valid Γ Δ
-- `co` is Containment for the language [p, q, r], as `coEntries`; by theorem,
-- every classically valid sequent over p, q, r is derivable over it, and over
-- any base with it added.
example : co = [] ++ coEntries [0, 1, 2] := rfl
example (Γ Δ : List (Formula Nat)) (hΓ : ∀ φ ∈ Γ, ∀ a ∈ φ.atoms, a ∈ [0, 1, 2])
    (hΔ : ∀ φ ∈ Δ, ∀ a ∈ φ.atoms, a ∈ [0, 1, 2]) (h : Valid Γ Δ) :
    Derivable (baseRel co) Γ Δ :=
  supraclassical_coEntries [] [0, 1, 2] hΓ hΔ h
example : Derivable (baseRel (pq ++ coEntries [0, 1, 2])) [] [disj p (neg p)] :=
  supraclassical_coEntries pq [0, 1, 2] (by decide) (by decide)
    (fun v _ => ⟨_, List.mem_singleton_self _, by simp [Formula.eval]⟩)
example : Derivable (baseRel (pq ++ coEntries [0, 1])) [conj p (neg q), r] [conj p (neg q)] :=
  overlap_derivable_coEntries pq [0, 1] (conj p (neg q)) (by decide) (by simp) (by simp)
example : (baseRel (coEntries [0, 1])).ContainmentOn [0, 1] :=
  containmentOn_coEntries [] [0, 1]
-- Containment for [p, q] says nothing about r.
example : ¬ Derivable (baseRel (coEntries [0, 1])) [r] [r] := by decide
example : ¬ (baseRel (coEntries [0, 1])).Containment := fun h =>
  absurd (h [2] [2] ⟨2, by simp, by simp⟩) (by decide)

/-! ### The book's instances whose context keeps the principal sentence -/

-- In `Γ, ¬p ⇒ Δ` the context `Γ` may itself contain `¬p`.
example : Derivable (baseRel co) [neg p] [neg p] :=
  Derivable.negL (Γ₀ := [neg p]) (A := p) (setEq_cons_self (by simp)) (by decide)
-- The certificate checker accepts such a step (`keep = true`) ...
example : check (baseRel co)
    (.node false (disj p (neg p)) true
      (.node false (disj p (neg p)) false
        (.node false (neg p) false .ax .ax .ax) .ax .ax) .ax .ax)
    [] [disj p (neg p)] = true := by decide
-- ... and still refuses it when a leaf is not in the base.
example : check (baseRel empty)
    (.node false (disj p (neg p)) true
      (.node false (disj p (neg p)) false
        (.node false (neg p) false .ax .ax .ax) .ax .ax) .ax .ax)
    [] [disj p (neg p)] = false := by decide

/-! ### Refutations -/

example : refute (baseRel empty) [] [p] [p] = true := by decide
example : refute (baseRel pq) [] [p] [q] = false := by decide
example : refute (baseRel rconj) [⟨false, conj p q, 2⟩] [] [conj p q] = true := by decide
-- `findRefute` (what `nmms-lean` runs) returns an accepted refutation, and
-- nothing on a derivable sequent.
example : (match findRefute (baseRel rconj) [] [conj p q] with
    | some c => refute (baseRel rconj) c [] [conj p q]
    | none => false) = true := by decide
example : (findRefute (baseRel rconj) [] [conj p q]).map List.length = some 1 := by decide
example : (findRefute (baseRel pq) [p] [q]).isSome = false := by decide
example : (match findRefute (baseRel empty) [p] [p] with
    | some c => refute (baseRel empty) c [p] [p]
    | none => false) = true := by decide

/-! ### The theorems' statements, pinned -/

example (B : List (Entry Nat)) (Γ Δ : List (Formula Nat)) :
    fastProve (baseRel B) Γ Δ = true ↔ Derivable (baseRel B) Γ Δ := (reasoner_correct B Γ Δ).1
example (B : List (Entry Nat)) (Γ Δ : List (Formula Nat)) (hg : allAtomic Γ = true)
    (hd : allAtomic Δ = true) :
    Derivable (baseRel B) Γ Δ ↔ baseRel B (atomsOf Γ) (atomsOf Δ) = true :=
  derivable_atomic_iff hg hd
example (B : List (Entry Nat)) (Γ Δ : List (Formula Nat)) :
    (∃ c, check (baseRel B) c Γ Δ = true) ↔ Derivable (baseRel B) Γ Δ :=
  certifiable_iff (baseRel_setInvariant B) Γ Δ
example (B : List (Entry Nat)) (Γ Δ : List (Formula Nat)) :
    (∃ c, refute (baseRel B) c Γ Δ = true) ↔ ¬ Derivable (baseRel B) Γ Δ :=
  refutable_iff (baseRel_setInvariant B) Γ Δ
example (B : List (Entry Nat)) (Γ Δ : List (Formula Nat)) (c : List (Step Nat))
    (h : findRefute (baseRel B) Γ Δ = some c) : refute (baseRel B) c Γ Δ = true :=
  findRefute_sound h
example (B : List (Entry Nat)) (Γ Δ : List (Formula Nat)) (h : ¬ Derivable (baseRel B) Γ Δ) :
    ∃ c, findRefute (baseRel B) Γ Δ = some c ∧ refute (baseRel B) c Γ Δ = true :=
  findRefute_complete h
-- "refute_ok" as `nmms-lean` computes it is exactly non-derivability. (Each
-- `match` is its own auxiliary definition, so the two statements agree once
-- the result of `findRefute` is split.)
example (B : List (Entry Nat)) (Γ Δ : List (Formula Nat)) :
    (match findRefute (baseRel B) Γ Δ with
      | some c => refute (baseRel B) c Γ Δ
      | none => false) = true ↔ ¬ Derivable (baseRel B) Γ Δ := by
  have h := refuteOk_iff (baseRel_setInvariant B) Γ Δ
  revert h
  cases findRefute (baseRel B) Γ Δ <;> exact id
example (B : List (Entry Nat)) (L : List Nat) :
    (baseRel (B ++ coEntries L)).ContainmentOn L := containmentOn_coEntries B L
example (R : BaseRel Nat) (L : List Nat) (hC : R.ContainmentOn L) (Γ Δ : List (Formula Nat))
    (hΓ : ∀ φ ∈ Γ, ∀ a ∈ φ.atoms, a ∈ L) (hΔ : ∀ φ ∈ Δ, ∀ a ∈ φ.atoms, a ∈ L)
    (h : Valid Γ Δ) : Derivable R Γ Δ :=
  supraclassical_on hC hΓ hΔ h
example (R : BaseRel Nat) (L : List Nat) (hC : R.ContainmentOn L) (φ : Formula Nat)
    (Γ Δ : List (Formula Nat)) (hL : ∀ a ∈ φ.atoms, a ∈ L) (h1 : φ ∈ Γ) (h2 : φ ∈ Δ) :
    Derivable R Γ Δ :=
  overlap_derivable_on hC φ hL h1 h2
example (B : List (Entry Nat)) (L : List Nat) (Γ Δ : List (Formula Nat))
    (hΓ : ∀ φ ∈ Γ, ∀ a ∈ φ.atoms, a ∈ L) (hΔ : ∀ φ ∈ Δ, ∀ a ∈ φ.atoms, a ∈ L)
    (h : Valid Γ Δ) : Derivable (baseRel (B ++ coEntries L)) Γ Δ :=
  supraclassical_coEntries B L hΓ hΔ h
example (B : List (Entry Nat)) (L : List Nat) (φ : Formula Nat) (Γ Δ : List (Formula Nat))
    (hL : ∀ a ∈ φ.atoms, a ∈ L) (h1 : φ ∈ Γ) (h2 : φ ∈ Δ) :
    Derivable (baseRel (B ++ coEntries L)) Γ Δ :=
  overlap_derivable_coEntries B L φ hL h1 h2

end NmmsRulesTests
