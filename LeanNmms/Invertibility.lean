/-
  LeanNmms.Invertibility

  Proof of `NMMS.Invertibility` (the book's Prop. 27, as reported), by
  characterizing derivability through the leaves of a complete
  decomposition.

  Why this route. Permuting rules inside a derivation needs an absorption
  lemma for every pair of rules, because a sentence removed by one rule can
  be produced again as a part by another. Here, instead:

  * `C s φ X Y` (a *contribution*): one branch of fully decomposing `φ` on
    side `s` (`true` = left) leaves the atoms `X` on the left and `Y` on the
    right. Atom lists are read as sets, and every relation used is closed
    under set equality.
  * `Leaves Γ Δ X Y`: one contribution from every member of each side,
    combined. `LeafValid R Γ Δ`: every leaf is in the base. Only the base
    counts: a leaf whose sides share an atom is not an axiom unless the base
    contains it.
  * `C_uc` is the single absorption lemma: contributions are closed under
    union. That holds because of the third premises (L∨, R∧, L→ allow both
    parts at once). So a sentence that occurs twice contributes exactly what
    it contributes once (`S_congr`: the leaves depend only on the sets).
    This is also why the book's rule instances whose context keeps the
    principal sentence change nothing.
  * Each rule's conclusion has exactly the leaves of its premises together
    (`*_sem` lemmas, for any context), so `derivable_iff_valid` holds:
    soundness by induction on derivations, completeness by the
    connective-count measure (`derivable_of_preserved`). Invertibility
    follows immediately.
-/
import LeanNmms.Open
import LeanNmms.Containment

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-! ### Set equality of atom lists -/

/-- Closes set-equality goals between appends of lists, using the set-equality
hypotheses in context. -/
macro "seteq" : tactic =>
  `(tactic| (simp only [SetEq] at *; intro x; simp only [List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, false_or] at *; grind))

/-! ### Relations on pairs of atom lists -/

/-- A set of atomic sequents, as a predicate on (left atoms, right atoms). -/
abbrev Rel2 (α : Type) := List α → List α → Prop

/-- The empty sequent only. -/
def E : Rel2 α := fun X Y => SetEq X [] ∧ SetEq Y []

/-- Combine one member of `P` with one member of `Q`. -/
def Prod2 (P Q : Rel2 α) : Rel2 α := fun X Y =>
  ∃ X1 Y1 X2 Y2, P X1 Y1 ∧ Q X2 Y2 ∧ SetEq X (X1 ++ X2) ∧ SetEq Y (Y1 ++ Y2)

/-- Either part alone, or both together (the shape of the three-premise rules). -/
def Opt (P Q : Rel2 α) : Rel2 α := fun X Y => P X Y ∨ Q X Y ∨ Prod2 P Q X Y

/-- Same members. -/
def PEq (P Q : Rel2 α) : Prop := ∀ X Y, P X Y ↔ Q X Y

/-- Closed under set equality. -/
def Cl (P : Rel2 α) : Prop :=
  ∀ {X Y X' Y'}, P X Y → SetEq X X' → SetEq Y Y' → P X' Y'

/-- Closed under union. -/
def UC (P : Rel2 α) : Prop :=
  ∀ {X1 Y1 X2 Y2}, P X1 Y1 → P X2 Y2 → P (X1 ++ X2) (Y1 ++ Y2)

/-- **Contributions** of a sentence on a side (`true` = left). -/
def C : Bool → Formula α → Rel2 α
  | true, atom p => fun X Y => SetEq X [p] ∧ SetEq Y []
  | false, atom p => fun X Y => SetEq X [] ∧ SetEq Y [p]
  | s, neg A => C (!s) A
  | true, conj A B => Prod2 (C true A) (C true B)
  | false, conj A B => Opt (C false A) (C false B)
  | true, disj A B => Opt (C true A) (C true B)
  | false, disj A B => Prod2 (C false A) (C false B)
  | true, impl A B => Opt (C false A) (C true B)
  | false, impl A B => Prod2 (C true A) (C false B)

/-- Contributions of a whole side. -/
def S (s : Bool) : List (Formula α) → Rel2 α
  | [] => E
  | φ :: l => Prod2 (C s φ) (S s l)

/-- The leaves of a complete decomposition of `Γ ⇒ Δ`. -/
def Leaves (Γ Δ : List (Formula α)) : Rel2 α := Prod2 (S true Γ) (S false Δ)

/-- An atomic sequent that is an axiom: one in the base. -/
def AxA (R : BaseRel α) : Rel2 α := fun X Y => R X Y = true

/-- Every member of `P` is an axiom. -/
def AllAx (R : BaseRel α) (P : Rel2 α) : Prop := ∀ X Y, P X Y → AxA R X Y

/-- Every leaf of `Γ ⇒ Δ` is in the base. -/
def LeafValid (R : BaseRel α) (Γ Δ : List (Formula α)) : Prop := AllAx R (Leaves Γ Δ)

/-! ### Closure under set equality -/

theorem Prod2_cl {P Q : Rel2 α} : Cl (Prod2 P Q) := by
  intro X Y X' Y' ⟨X1, Y1, X2, Y2, h1, h2, hx, hy⟩ ex ey
  exact ⟨X1, Y1, X2, Y2, h1, h2, ex.symm.trans hx, ey.symm.trans hy⟩

theorem Opt_cl {P Q : Rel2 α} (hP : Cl P) (hQ : Cl Q) : Cl (Opt P Q) := by
  intro X Y X' Y' h ex ey
  rcases h with h | h | h
  · exact Or.inl (hP h ex ey)
  · exact Or.inr (Or.inl (hQ h ex ey))
  · exact Or.inr (Or.inr (Prod2_cl h ex ey))

theorem C_cl : ∀ (φ : Formula α) (s : Bool), Cl (C s φ) := by
  intro φ
  induction φ with
  | atom p =>
    intro s; cases s
    · intro X Y X' Y' ⟨h1, h2⟩ ex ey; exact ⟨ex.symm.trans h1, ey.symm.trans h2⟩
    · intro X Y X' Y' ⟨h1, h2⟩ ex ey; exact ⟨ex.symm.trans h1, ey.symm.trans h2⟩
  | neg A ih => intro s; cases s <;> exact ih _
  | conj A B ihA ihB => intro s; cases s; exact Opt_cl (ihA _) (ihB _); exact Prod2_cl
  | disj A B ihA ihB => intro s; cases s; exact Prod2_cl; exact Opt_cl (ihA _) (ihB _)
  | impl A B ihA ihB => intro s; cases s; exact Prod2_cl; exact Opt_cl (ihA _) (ihB _)

/-! ### Closure under union: the one absorption lemma -/

theorem E_uc : UC (E : Rel2 α) := by
  intro X1 Y1 X2 Y2 ⟨a1, b1⟩ ⟨a2, b2⟩; exact ⟨by seteq, by seteq⟩

theorem Prod2_uc {P Q : Rel2 α} (hP : UC P) (hQ : UC Q) : UC (Prod2 P Q) := by
  intro X1 Y1 X2 Y2 ⟨A1, B1, A2, B2, p1, q1, hx1, hy1⟩ ⟨A1', B1', A2', B2', p2, q2, hx2, hy2⟩
  exact ⟨A1 ++ A1', B1 ++ B1', A2 ++ A2', B2 ++ B2', hP p1 p2, hQ q1 q2, by seteq, by seteq⟩

theorem Opt_uc {P Q : Rel2 α} (hP : UC P) (hQ : UC Q) : UC (Opt P Q) := by
  intro X1 Y1 X2 Y2 h1 h2
  rcases h1 with p1 | q1 | ⟨A1, B1, A2, B2, p1, q1, hx1, hy1⟩ <;>
  rcases h2 with p2 | q2 | ⟨A1', B1', A2', B2', p2, q2, hx2, hy2⟩
  · exact Or.inl (hP p1 p2)
  · exact Or.inr (Or.inr ⟨X1, Y1, X2, Y2, p1, q2, SetEq.rfl', SetEq.rfl'⟩)
  · exact Or.inr (Or.inr ⟨X1 ++ A1', Y1 ++ B1', A2', B2', hP p1 p2, q2, by seteq, by seteq⟩)
  · exact Or.inr (Or.inr ⟨X2, Y2, X1, Y1, p2, q1, by seteq, by seteq⟩)
  · exact Or.inr (Or.inl (hQ q1 q2))
  · exact Or.inr (Or.inr ⟨A1', B1', X1 ++ A2', Y1 ++ B2', p2, hQ q1 q2, by seteq, by seteq⟩)
  · exact Or.inr (Or.inr ⟨A1 ++ X2, B1 ++ Y2, A2, B2, hP p1 p2, q1, by seteq, by seteq⟩)
  · exact Or.inr (Or.inr ⟨A1, B1, A2 ++ X2, B2 ++ Y2, p1, hQ q1 q2, by seteq, by seteq⟩)
  · exact Or.inr (Or.inr (Prod2_uc hP hQ ⟨A1, B1, A2, B2, p1, q1, hx1, hy1⟩
      ⟨A1', B1', A2', B2', p2, q2, hx2, hy2⟩))

/-- **Absorption.** Every sentence's contributions are closed under union, so
a sentence occurring twice contributes what it contributes once. -/
theorem C_uc : ∀ (φ : Formula α) (s : Bool), UC (C s φ) := by
  intro φ
  induction φ with
  | atom p =>
    intro s; cases s
    · intro X1 Y1 X2 Y2 ⟨a1, b1⟩ ⟨a2, b2⟩; exact ⟨by seteq, by seteq⟩
    · intro X1 Y1 X2 Y2 ⟨a1, b1⟩ ⟨a2, b2⟩; exact ⟨by seteq, by seteq⟩
  | neg A ih => intro s; cases s <;> exact ih _
  | conj A B ihA ihB =>
    intro s; cases s; exact Opt_uc (ihA _) (ihB _); exact Prod2_uc (ihA _) (ihB _)
  | disj A B ihA ihB =>
    intro s; cases s; exact Prod2_uc (ihA _) (ihB _); exact Opt_uc (ihA _) (ihB _)
  | impl A B ihA ihB =>
    intro s; cases s; exact Prod2_uc (ihA _) (ihB _); exact Opt_uc (ihA _) (ihB _)

theorem S_uc (s : Bool) : ∀ l : List (Formula α), UC (S s l)
  | [] => E_uc
  | φ :: l => Prod2_uc (C_uc φ s) (S_uc s l)

/-! ### Algebra of combination -/

theorem PEq.rfl' {P : Rel2 α} : PEq P P := fun _ _ => Iff.rfl
theorem PEq.symm {P Q : Rel2 α} (h : PEq P Q) : PEq Q P := fun X Y => (h X Y).symm
theorem PEq.trans {P Q T : Rel2 α} (h1 : PEq P Q) (h2 : PEq Q T) : PEq P T :=
  fun X Y => (h1 X Y).trans (h2 X Y)

theorem Prod2_congr {P P' Q Q' : Rel2 α} (h1 : PEq P P') (h2 : PEq Q Q') :
    PEq (Prod2 P Q) (Prod2 P' Q') := by
  intro X Y; constructor
  · rintro ⟨A, B, A', B', p, q, hx, hy⟩; exact ⟨A, B, A', B', (h1 _ _).mp p, (h2 _ _).mp q, hx, hy⟩
  · rintro ⟨A, B, A', B', p, q, hx, hy⟩; exact ⟨A, B, A', B', (h1 _ _).mpr p, (h2 _ _).mpr q, hx, hy⟩

theorem Prod2_comm {P Q : Rel2 α} : PEq (Prod2 P Q) (Prod2 Q P) := by
  intro X Y; constructor
  · rintro ⟨A, B, A', B', p, q, hx, hy⟩; exact ⟨A', B', A, B, q, p, by seteq, by seteq⟩
  · rintro ⟨A, B, A', B', p, q, hx, hy⟩; exact ⟨A', B', A, B, q, p, by seteq, by seteq⟩

theorem Prod2_assoc {P Q K : Rel2 α} : PEq (Prod2 (Prod2 P Q) K) (Prod2 P (Prod2 Q K)) := by
  intro X Y; constructor
  · rintro ⟨A, B, A3, B3, ⟨A1, B1, A2, B2, p, q, hx', hy'⟩, k, hx, hy⟩
    exact ⟨A1, B1, A2 ++ A3, B2 ++ B3, p, ⟨A2, B2, A3, B3, q, k, SetEq.rfl', SetEq.rfl'⟩,
      by seteq, by seteq⟩
  · rintro ⟨A1, B1, A, B, p, ⟨A2, B2, A3, B3, q, k, hx', hy'⟩, hx, hy⟩
    exact ⟨A1 ++ A2, B1 ++ B2, A3, B3, ⟨A1, B1, A2, B2, p, q, SetEq.rfl', SetEq.rfl'⟩, k,
      by seteq, by seteq⟩

theorem Prod2_swap {P Q K : Rel2 α} : PEq (Prod2 P (Prod2 Q K)) (Prod2 Q (Prod2 P K)) :=
  Prod2_assoc.symm.trans ((Prod2_congr Prod2_comm PEq.rfl').trans Prod2_assoc)

theorem Prod2_idem {P K : Rel2 α} (hP : UC P) : PEq (Prod2 P (Prod2 P K)) (Prod2 P K) := by
  intro X Y; constructor
  · rintro ⟨A1, B1, A, B, p1, ⟨A2, B2, A3, B3, p2, k, hx', hy'⟩, hx, hy⟩
    exact ⟨A1 ++ A2, B1 ++ B2, A3, B3, hP p1 p2, k, by seteq, by seteq⟩
  · rintro ⟨A1, B1, A3, B3, p, k, hx, hy⟩
    exact ⟨A1, B1, A1 ++ A3, B1 ++ B3, p, ⟨A1, B1, A3, B3, p, k, SetEq.rfl', SetEq.rfl'⟩,
      by seteq, by seteq⟩

theorem Prod2_opt {P Q K : Rel2 α} : PEq (Prod2 (Opt P Q) K)
    (fun X Y => Prod2 P K X Y ∨ Prod2 Q K X Y ∨ Prod2 P (Prod2 Q K) X Y) := by
  intro X Y; constructor
  · rintro ⟨A, B, A', B', o, k, hx, hy⟩
    rcases o with p | q | pq
    · exact Or.inl ⟨A, B, A', B', p, k, hx, hy⟩
    · exact Or.inr (Or.inl ⟨A, B, A', B', q, k, hx, hy⟩)
    · exact Or.inr (Or.inr ((Prod2_assoc _ _).mp ⟨A, B, A', B', pq, k, hx, hy⟩))
  · rintro (⟨A, B, A', B', p, k, hx, hy⟩ | ⟨A, B, A', B', q, k, hx, hy⟩ | h)
    · exact ⟨A, B, A', B', Or.inl p, k, hx, hy⟩
    · exact ⟨A, B, A', B', Or.inr (Or.inl q), k, hx, hy⟩
    · obtain ⟨A, B, A', B', pq, k, hx, hy⟩ := (Prod2_assoc _ _).mpr h
      exact ⟨A, B, A', B', Or.inr (Or.inr pq), k, hx, hy⟩

/-! ### A side, one member at a time -/

theorem rest_cons_self (φ : Formula α) (l : List (Formula α)) :
    rest (φ :: l) φ = rest l φ := by simp [rest]

theorem rest_cons_ne {x φ : Formula α} (h : x ≠ φ) (l : List (Formula α)) :
    rest (x :: l) φ = x :: rest l φ := by simp [rest, h]

theorem rest_of_not_mem {φ : Formula α} {l : List (Formula α)} (h : φ ∉ l) :
    rest l φ = l := by
  unfold rest
  apply List.filter_eq_self.mpr
  intro a ha
  have : a ≠ φ := by rintro rfl; exact h ha
  simp [this]

/-- A member's contribution can be split off from its side, with every copy
of it removed (this is where absorption is used). -/
theorem S_mem (s : Bool) (φ : Formula α) : ∀ (l : List (Formula α)), φ ∈ l →
    PEq (S s l) (Prod2 (C s φ) (S s (rest l φ)))
  | [], h => absurd h (by simp)
  | x :: l, h => by
    by_cases hx : x = φ
    · subst hx
      rw [rest_cons_self]
      by_cases hl : x ∈ l
      · exact (Prod2_congr PEq.rfl' (S_mem s x l hl)).trans (Prod2_idem (C_uc x s))
      · rw [rest_of_not_mem hl]; exact PEq.rfl'
    · have hl : φ ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      rw [rest_cons_ne hx]
      exact (Prod2_congr PEq.rfl' (S_mem s φ l hl)).trans Prod2_swap


theorem length_rest_lt {φ : Formula α} {l : List (Formula α)} (h : φ ∈ l) :
    (rest l φ).length < l.length := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    by_cases hx : x = φ
    · subst hx
      rw [rest_cons_self]
      have : (rest l x).length ≤ l.length := List.length_filter_le _ _
      simp only [List.length_cons]; omega
    · rw [rest_cons_ne hx]
      have hl : φ ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      simp only [List.length_cons]; have := ih hl; omega

/-- **The leaves depend only on the sets**: a side's contributions are the same
for any two lists with the same members (absorption, via `S_mem`). -/
theorem S_congr (s : Bool) : ∀ (n : Nat) (l l' : List (Formula α)), l.length < n →
    SetEq l l' → PEq (S s l) (S s l')
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], l', _, e => by
    cases l' with
    | nil => exact PEq.rfl'
    | cons x t => exact absurd ((e x).mpr (List.mem_cons_self ..)) (by simp)
  | n + 1, x :: t, l', hl, e => by
    have hx : x ∈ x :: t := List.mem_cons_self ..
    have hx' : x ∈ l' := (e x).mp hx
    have hlen := length_rest_lt hx
    have ih := S_congr s n (rest (x :: t) x) (rest l' x) (by simp at hl hlen ⊢; omega) (e.rest x)
    exact (S_mem s x (x :: t) hx).trans ((Prod2_congr PEq.rfl' ih).trans (S_mem s x l' hx').symm)

theorem Leaves_congr {Γ Γ' Δ Δ' : List (Formula α)} (e1 : SetEq Γ Γ') (e2 : SetEq Δ Δ') :
    PEq (Leaves Γ Δ) (Leaves Γ' Δ') :=
  Prod2_congr (S_congr true _ Γ Γ' (Nat.lt_succ_self _) e1)
    (S_congr false _ Δ Δ' (Nat.lt_succ_self _) e2)

theorem Leaves_consL (A : Formula α) (Γ Δ : List (Formula α)) :
    PEq (Leaves (A :: Γ) Δ) (Prod2 (C true A) (Leaves Γ Δ)) := Prod2_assoc

theorem Leaves_consR (A : Formula α) (Γ Δ : List (Formula α)) :
    PEq (Leaves Γ (A :: Δ)) (Prod2 (C false A) (Leaves Γ Δ)) := Prod2_swap

/-! ### Every rule is an equivalence on leaves -/

theorem AllAx_congr {R : BaseRel α} {P Q : Rel2 α} (h : PEq P Q) : AllAx R P ↔ AllAx R Q :=
  ⟨fun hp X Y q => hp X Y ((h X Y).mpr q), fun hq X Y p => hq X Y ((h X Y).mp p)⟩

theorem LeafValid_congr {R : BaseRel α} {Γ Γ' Δ Δ' : List (Formula α)} (e1 : SetEq Γ Γ')
    (e2 : SetEq Δ Δ') : LeafValid R Γ Δ ↔ LeafValid R Γ' Δ' :=
  AllAx_congr (Leaves_congr e1 e2)

theorem AllAx_or3 {R : BaseRel α} {P Q T : Rel2 α} :
    AllAx R (fun X Y => P X Y ∨ Q X Y ∨ T X Y) ↔ AllAx R P ∧ AllAx R Q ∧ AllAx R T := by
  constructor
  · intro h
    exact ⟨fun X Y p => h X Y (Or.inl p), fun X Y q => h X Y (Or.inr (Or.inl q)),
      fun X Y t => h X Y (Or.inr (Or.inr t))⟩
  · rintro ⟨h1, h2, h3⟩ X Y (p | q | t)
    · exact h1 X Y p
    · exact h2 X Y q
    · exact h3 X Y t

theorem one_sem {R : BaseRel α} {S0 S1 T : Rel2 α} (h0 : PEq S0 T) (h1 : PEq S1 T) :
    AllAx R S0 ↔ AllAx R S1 :=
  (AllAx_congr h0).trans (AllAx_congr h1).symm

theorem opt_sem {R : BaseRel α} {S0 S1 S2 S3 P Q K : Rel2 α} (h0 : PEq S0 (Prod2 (Opt P Q) K))
    (h1 : PEq S1 (Prod2 P K)) (h2 : PEq S2 (Prod2 Q K)) (h3 : PEq S3 (Prod2 P (Prod2 Q K))) :
    AllAx R S0 ↔ AllAx R S1 ∧ AllAx R S2 ∧ AllAx R S3 := by
  rw [AllAx_congr (h0.trans Prod2_opt), AllAx_or3, AllAx_congr h1, AllAx_congr h2,
    AllAx_congr h3]

variable {R : BaseRel α} {Γ Δ : List (Formula α)} {A B : Formula α}

/-! The book's form: the context `Γ` is arbitrary (it may contain the
principal sentence). -/

theorem negL_sem : LeafValid R (neg A :: Γ) Δ ↔ LeafValid R Γ (A :: Δ) :=
  one_sem (Leaves_consL (neg A) Γ Δ) (Leaves_consR A _ _)

theorem implL_sem : LeafValid R (impl A B :: Γ) Δ ↔
    LeafValid R Γ (A :: Δ) ∧ LeafValid R (B :: Γ) Δ ∧ LeafValid R (B :: Γ) (A :: Δ) :=
  opt_sem (P := C false A) (Q := C true B) (Leaves_consL (impl A B) Γ Δ) (Leaves_consR A _ _)
    (Leaves_consL B _ _)
    ((Leaves_consL B _ _).trans ((Prod2_congr PEq.rfl' (Leaves_consR A _ _)).trans Prod2_swap))

theorem conjL_sem : LeafValid R (conj A B :: Γ) Δ ↔ LeafValid R (A :: B :: Γ) Δ :=
  one_sem ((Leaves_consL (conj A B) Γ Δ).trans Prod2_assoc)
    ((Leaves_consL A _ _).trans (Prod2_congr PEq.rfl' (Leaves_consL B _ _)))

theorem disjL_sem : LeafValid R (disj A B :: Γ) Δ ↔
    LeafValid R (A :: Γ) Δ ∧ LeafValid R (B :: Γ) Δ ∧ LeafValid R (A :: B :: Γ) Δ :=
  opt_sem (P := C true A) (Q := C true B) (Leaves_consL (disj A B) Γ Δ) (Leaves_consL A _ _)
    (Leaves_consL B _ _) ((Leaves_consL A _ _).trans (Prod2_congr PEq.rfl' (Leaves_consL B _ _)))

theorem negR_sem : LeafValid R Γ (neg A :: Δ) ↔ LeafValid R (A :: Γ) Δ :=
  one_sem (Leaves_consR (neg A) Γ Δ) (Leaves_consL A _ _)

theorem implR_sem : LeafValid R Γ (impl A B :: Δ) ↔ LeafValid R (A :: Γ) (B :: Δ) :=
  one_sem ((Leaves_consR (impl A B) Γ Δ).trans Prod2_assoc)
    ((Leaves_consL A _ _).trans (Prod2_congr PEq.rfl' (Leaves_consR B _ _)))

theorem conjR_sem : LeafValid R Γ (conj A B :: Δ) ↔
    LeafValid R Γ (A :: Δ) ∧ LeafValid R Γ (B :: Δ) ∧ LeafValid R Γ (A :: B :: Δ) :=
  opt_sem (P := C false A) (Q := C false B) (Leaves_consR (conj A B) Γ Δ) (Leaves_consR A _ _)
    (Leaves_consR B _ _) ((Leaves_consR A _ _).trans (Prod2_congr PEq.rfl' (Leaves_consR B _ _)))

theorem disjR_sem : LeafValid R Γ (disj A B :: Δ) ↔ LeafValid R Γ (A :: B :: Δ) :=
  one_sem ((Leaves_consR (disj A B) Γ Δ).trans Prod2_assoc)
    ((Leaves_consR A _ _).trans (Prod2_congr PEq.rfl' (Leaves_consR B _ _)))

/-! The form the decision procedures use: the principal sentence is a member
of its side and is removed from the context. -/

theorem memL_sem {φ : Formula α} (h : φ ∈ Γ) {T : Prop}
    (hs : LeafValid R (φ :: rest Γ φ) Δ ↔ T) : LeafValid R Γ Δ ↔ T :=
  (LeafValid_congr (setEq_cons_rest h) SetEq.rfl').trans hs

theorem memR_sem {φ : Formula α} (h : φ ∈ Δ) {T : Prop}
    (hs : LeafValid R Γ (φ :: rest Δ φ) ↔ T) : LeafValid R Γ Δ ↔ T :=
  (LeafValid_congr SetEq.rfl' (setEq_cons_rest h)).trans hs

/-! ### Atomic sequents -/

theorem allAtomic_cons {φ : Formula α} {l : List (Formula α)} (h : allAtomic (φ :: l) = true) :
    (∃ a, φ = atom a) ∧ allAtomic l = true :=
  ⟨isAtom_iff.mp ((allAtomic_iff.mp h) φ (by simp)),
    allAtomic_iff.mpr (fun ψ hψ => allAtomic_iff.mp h ψ (by simp [hψ]))⟩

theorem S_true_atomic : ∀ (l : List (Formula α)), allAtomic l = true →
    S true l (atomsOf l) []
  | [], _ => ⟨SetEq.rfl', SetEq.rfl'⟩
  | φ :: l, h => by
    obtain ⟨⟨a, rfl⟩, h2⟩ := allAtomic_cons h
    exact ⟨[a], [], atomsOf l, [], ⟨SetEq.rfl', SetEq.rfl'⟩, S_true_atomic l h2,
      fun x => by simp [atomsOf], SetEq.rfl'⟩

theorem S_false_atomic : ∀ (l : List (Formula α)), allAtomic l = true →
    S false l [] (atomsOf l)
  | [], _ => ⟨SetEq.rfl', SetEq.rfl'⟩
  | φ :: l, h => by
    obtain ⟨⟨a, rfl⟩, h2⟩ := allAtomic_cons h
    exact ⟨[], [a], [], atomsOf l, ⟨SetEq.rfl', SetEq.rfl'⟩, S_false_atomic l h2,
      SetEq.rfl', fun x => by simp [atomsOf]⟩

theorem S_true_atomic_inv : ∀ (l : List (Formula α)), allAtomic l = true →
    ∀ X Y, S true l X Y → SetEq X (atomsOf l) ∧ SetEq Y []
  | [], _, _, _, h => h
  | φ :: l, h, X, Y, hs => by
    obtain ⟨⟨a, rfl⟩, h2⟩ := allAtomic_cons h
    obtain ⟨X1, Y1, X2, Y2, ⟨e1, e2⟩, hs', hx, hy⟩ := hs
    obtain ⟨e3, e4⟩ := S_true_atomic_inv l h2 X2 Y2 hs'
    simp only [atomsOf]
    exact ⟨by seteq, by seteq⟩

theorem S_false_atomic_inv : ∀ (l : List (Formula α)), allAtomic l = true →
    ∀ X Y, S false l X Y → SetEq X [] ∧ SetEq Y (atomsOf l)
  | [], _, _, _, h => h
  | φ :: l, h, X, Y, hs => by
    obtain ⟨⟨a, rfl⟩, h2⟩ := allAtomic_cons h
    obtain ⟨X1, Y1, X2, Y2, ⟨e1, e2⟩, hs', hx, hy⟩ := hs
    obtain ⟨e3, e4⟩ := S_false_atomic_inv l h2 X2 Y2 hs'
    simp only [atomsOf]
    exact ⟨by seteq, by seteq⟩

/-! ### Derivability is validity of the leaves -/

/-- Soundness of the leaf semantics: a derivable sequent has only leaves in
the base. -/
theorem valid_of_derivable (hR : R.SetInvariant) (h : Derivable R Γ Δ) : LeafValid R Γ Δ := by
  induction h with
  | @ax Γ Δ hg hd hb =>
    intro X Y ⟨X1, Y1, X2, Y2, h1, h2, hx, hy⟩
    obtain ⟨e1, e2⟩ := S_true_atomic_inv Γ hg X1 Y1 h1
    obtain ⟨e3, e4⟩ := S_false_atomic_inv Δ hd X2 Y2 h2
    have ex : SetEq X (atomsOf Γ) := by seteq
    have ey : SetEq Y (atomsOf Δ) := by seteq
    show R X Y = true
    rw [hR _ _ _ _ ex ey]; exact hb
  | negL e _ ih => exact (LeafValid_congr e SetEq.rfl').mpr (negL_sem.mpr ih)
  | implL e _ _ _ ih1 ih2 ih3 =>
    exact (LeafValid_congr e SetEq.rfl').mpr (implL_sem.mpr ⟨ih1, ih2, ih3⟩)
  | conjL e _ ih => exact (LeafValid_congr e SetEq.rfl').mpr (conjL_sem.mpr ih)
  | disjL e _ _ _ ih1 ih2 ih3 =>
    exact (LeafValid_congr e SetEq.rfl').mpr (disjL_sem.mpr ⟨ih1, ih2, ih3⟩)
  | negR e _ ih => exact (LeafValid_congr SetEq.rfl' e).mpr (negR_sem.mpr ih)
  | implR e _ ih => exact (LeafValid_congr SetEq.rfl' e).mpr (implR_sem.mpr ih)
  | conjR e _ _ _ ih1 ih2 ih3 =>
    exact (LeafValid_congr SetEq.rfl' e).mpr (conjR_sem.mpr ⟨ih1, ih2, ih3⟩)
  | disjR e _ ih => exact (LeafValid_congr SetEq.rfl' e).mpr (disjR_sem.mpr ih)

/-- Completeness of the leaf semantics: if every leaf is in the base, the
sequent is derivable (by decomposing in any order, always removing the
principal sentence from its side). -/
theorem derivable_of_valid (h : LeafValid R Γ Δ) : Derivable R Γ Δ := by
  refine derivable_of_preserved R (LeafValid R) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (measure Γ Δ + 1) Γ Δ (by omega) h
  · intro Γ Δ hg hd hv
    have := hv _ _ ⟨_, _, _, _, S_true_atomic Γ hg, S_false_atomic Δ hd, SetEq.rfl', SetEq.rfl'⟩
    simp only [AxA, List.append_nil, List.nil_append] at this
    exact Derivable.ax hg hd this
  · intro Γ Δ A hm hv; exact (memL_sem hm negL_sem).mp hv
  · intro Γ Δ A B hm hv; exact (memL_sem hm implL_sem).mp hv
  · intro Γ Δ A B hm hv; exact (memL_sem hm conjL_sem).mp hv
  · intro Γ Δ A B hm hv; exact (memL_sem hm disjL_sem).mp hv
  · intro Γ Δ A hm hv; exact (memR_sem hm negR_sem).mp hv
  · intro Γ Δ A B hm hv; exact (memR_sem hm implR_sem).mp hv
  · intro Γ Δ A B hm hv; exact (memR_sem hm conjR_sem).mp hv
  · intro Γ Δ A B hm hv; exact (memR_sem hm disjR_sem).mp hv

/-- **Characterization.** Over a set-invariant base, `Γ ⇒ Δ` is derivable
exactly when every leaf of its complete decomposition is in the base. -/
theorem derivable_iff_valid (hR : R.SetInvariant) : Derivable R Γ Δ ↔ LeafValid R Γ Δ :=
  ⟨valid_of_derivable hR, derivable_of_valid⟩

/-- **Invertibility of every rule** (the book's Prop. 27, as reported), in the
book's form: any context, the principal sentence possibly in it. -/
theorem invertibility : Invertibility α := by
  intro R hR Γ Δ A B
  simp only [derivable_iff_valid hR]
  exact ⟨negL_sem, implL_sem, conjL_sem, disjL_sem, negR_sem, implR_sem, conjR_sem, disjR_sem⟩

/-! ### The same, with the principal sentence removed from its side -/

theorem negL_inv (hR : R.SetInvariant) (h : neg A ∈ Γ) (hd : Derivable R Γ Δ) :
    Derivable R (rest Γ (neg A)) (A :: Δ) :=
  derivable_of_valid ((memL_sem h negL_sem).mp (valid_of_derivable hR hd))
theorem implL_inv (hR : R.SetInvariant) (h : impl A B ∈ Γ) (hd : Derivable R Γ Δ) :
    Derivable R (rest Γ (impl A B)) (A :: Δ) ∧ Derivable R (B :: rest Γ (impl A B)) Δ ∧
      Derivable R (B :: rest Γ (impl A B)) (A :: Δ) := by
  obtain ⟨h1, h2, h3⟩ := (memL_sem h implL_sem).mp (valid_of_derivable hR hd)
  exact ⟨derivable_of_valid h1, derivable_of_valid h2, derivable_of_valid h3⟩
theorem conjL_inv (hR : R.SetInvariant) (h : conj A B ∈ Γ) (hd : Derivable R Γ Δ) :
    Derivable R (A :: B :: rest Γ (conj A B)) Δ :=
  derivable_of_valid ((memL_sem h conjL_sem).mp (valid_of_derivable hR hd))
theorem disjL_inv (hR : R.SetInvariant) (h : disj A B ∈ Γ) (hd : Derivable R Γ Δ) :
    Derivable R (A :: rest Γ (disj A B)) Δ ∧ Derivable R (B :: rest Γ (disj A B)) Δ ∧
      Derivable R (A :: B :: rest Γ (disj A B)) Δ := by
  obtain ⟨h1, h2, h3⟩ := (memL_sem h disjL_sem).mp (valid_of_derivable hR hd)
  exact ⟨derivable_of_valid h1, derivable_of_valid h2, derivable_of_valid h3⟩
theorem negR_inv (hR : R.SetInvariant) (h : neg A ∈ Δ) (hd : Derivable R Γ Δ) :
    Derivable R (A :: Γ) (rest Δ (neg A)) :=
  derivable_of_valid ((memR_sem h negR_sem).mp (valid_of_derivable hR hd))
theorem implR_inv (hR : R.SetInvariant) (h : impl A B ∈ Δ) (hd : Derivable R Γ Δ) :
    Derivable R (A :: Γ) (B :: rest Δ (impl A B)) :=
  derivable_of_valid ((memR_sem h implR_sem).mp (valid_of_derivable hR hd))
theorem conjR_inv (hR : R.SetInvariant) (h : conj A B ∈ Δ) (hd : Derivable R Γ Δ) :
    Derivable R Γ (A :: rest Δ (conj A B)) ∧ Derivable R Γ (B :: rest Δ (conj A B)) ∧
      Derivable R Γ (A :: B :: rest Δ (conj A B)) := by
  obtain ⟨h1, h2, h3⟩ := (memR_sem h conjR_sem).mp (valid_of_derivable hR hd)
  exact ⟨derivable_of_valid h1, derivable_of_valid h2, derivable_of_valid h3⟩
theorem disjR_inv (hR : R.SetInvariant) (h : disj A B ∈ Δ) (hd : Derivable R Γ Δ) :
    Derivable R Γ (A :: B :: rest Δ (disj A B)) :=
  derivable_of_valid ((memR_sem h disjR_sem).mp (valid_of_derivable hR hd))

/-- **Keeping the principal sentence in the context changes nothing.** The
book's L¬ instance whose context still contains `¬A` has a derivable premise
exactly when the instance with `¬A` removed does (the other rules are alike,
by `invertibility`). -/
theorem negL_keep_iff (hR : R.SetInvariant) (h : neg A ∈ Γ) :
    Derivable R Γ (A :: Δ) ↔ Derivable R (rest Γ (neg A)) (A :: Δ) := by
  simp only [derivable_iff_valid hR]
  exact negL_sem.symm.trans
    ((LeafValid_congr (setEq_cons_self h) SetEq.rfl').symm.trans (memL_sem h negL_sem))

end NMMS
