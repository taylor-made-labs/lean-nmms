/-
  LeanNmms.Possibilistic — possibilistic NMMS (tracer N). STATEMENTS ONLY.

  This module is the graded theory, named apart from the book's NMMS: the
  book's calculus (`Derivable`, LeanNmms.Calculus) is unchanged, and every
  definition here reduces to it over a *cut* of a weighted base. Nothing in
  this file is a claim about Hlobil and Brandom's NMMS; it is a claim about
  weighted bases built on top of it, in the style of possibilistic logic
  (Dubois and Prade): each base entry carries a necessity-like weight in a
  scale with 0 and 1, and a sequent's *degree* is the largest threshold `t`
  at which the entries weighted `t` or more still derive it.

  Status (31 Oct 2026): every theorem marked `sorry` is a statement to be
  proved next, on this branch only; the branch is never merged with a
  `sorry`. `tests/AllConstantsAxioms.lean` fails on purpose until then.
  See docs/tracer-n.md for the state, the plan and the definition of done.

  Design decisions, with reasons:

  * The scale `W` is abstract: a total preorder with least element `zero`
    and greatest element `one`, decidable. Possibilistic logic is ordinal:
    only comparisons, min and max are ever used, never arithmetic. The unit
    interval is the intended instance; `Q01` (rationals in [0,1]) is the
    concrete, executable one. Antisymmetry is not assumed (unnormalised
    fractions compare equal both ways), so "the degree" is unique up to
    `≤` both ways, which is what `degree_sup_unique` states.
  * The threshold `t` can be 0, as Taylor asked (30 Oct), and the cut `B_0`
    is the whole base: an entry weighted 0 is in `B_0` and in no other cut
    (`cut_zero`). Because of that, the cut theorem at `t = 0` cannot read
    "degree ≥ 0 ↔ derivable over `B_0`" with a degree in [0,1] — degree ≥ 0
    would always hold. So the degree is an `Option W`: `none` means not
    derivable over any cut, `B_0` included; `some 0` means derivable over
    `B_0` only. `DegreeGe B t Γ Δ` is "the degree exists and is at least t".
  * The degree is computed, not merely specified: `degree?` takes the
    largest candidate threshold (0 or an entry's weight) at which the
    verified decision procedure `fastProve` (LeanNmms.Decide) accepts the
    sequent over the cut. Its specification is `cut_theorem`. The sup over
    all `t` in the scale is attained at a candidate: see `degree_sup`.
  * Combination of a source's own uncertainty with the holder's weight is
    `min` (`combine`), the possibilistic default: a claim is no more certain
    than the weaker of "I trust this source this much" and "the source is
    this sure". The source's supplied value is a preserved record on the
    graph side (graph-nmms), never overwritten by the combination.

  What follows from existing lemmas (no new proof idea):
  * `derivableAt_iff` is `reasoner_correct` (Decide.lean) over the cut.
  * `derivableAt_antitone` is `derivable_mono` + `baseRel_mono` + `cut_antitone`.
  * `derivableAt_zero_iff`, `derivableAt_lift` are rewrites with `cut_zero`,
    `cut_lift`.
  * `degree_none_iff`, `degree_sup`, `degree_sup_unique`, the decidability
    instance for `DegreeGe` and `degree_mono_base` all follow from
    `cut_theorem` and `derivableAt_antitone`.
  * `weakest_link_lower` and `weakest_link_attained` follow from
    `cut_theorem` and base monotonicity (`derivable_mono`), with
    `S := B.filter (d ≤ ·.weight)` as the witness of the second.
  New proofs needed: `derivable_mono` (induction on `Derivable`),
  `baseRel_mono` (`List.any` over a superset), `cut_zero`, `cut_antitone`,
  `cut_lift` (`List.filter` with a predicate that is always true, or
  implied), `cut_theorem` (the one real argument: given derivability at
  `t`, the least weight `m` of `cut B t` is a candidate with `t ≤ m` and
  `cut B m ⊇ cut B t`, and `maxList` of the derivable candidates is at
  least `m`), `Q01.le_trans` (cross-multiplication in `Nat`).
-/
import LeanNmms.Decide

namespace NMMS
namespace Possibilistic

/-- A possibilistic scale: a decidable total preorder with a least element
`zero` and a greatest element `one`. Every weight lies in `[zero, one]`
(`weight_bounds`). Only the order is used. -/
class Scale (W : Type) where
  le : W → W → Prop
  decLe : ∀ a b : W, Decidable (le a b)
  zero : W
  one : W
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_total : ∀ a b, le a b ∨ le b a
  zero_le : ∀ a, le zero a
  le_one : ∀ a, le a one

variable {W : Type} [Scale W]

instance : LE W := ⟨Scale.le⟩
instance (a b : W) : Decidable (a ≤ b) := Scale.decLe a b

theorem le_refl (a : W) : a ≤ a := Scale.le_refl a
theorem le_trans {a b c : W} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := Scale.le_trans h1 h2
theorem le_total (a b : W) : a ≤ b ∨ b ≤ a := Scale.le_total a b
theorem zero_le (a : W) : Scale.zero ≤ a := Scale.zero_le a
theorem le_one (a : W) : a ≤ Scale.one := Scale.le_one a

/-- **Weights lie in [0,1]**: every element of the scale is between its 0 and
its 1. -/
theorem weight_bounds (w : W) : Scale.zero ≤ w ∧ w ≤ Scale.one := ⟨zero_le w, le_one w⟩

/-! ### The unit interval, as rationals: the concrete scale -/

/-- A rational in `[0,1]`, as `num / den` with `num ≤ den` and `den > 0`.
Not normalised: `1/2` and `2/4` compare equal both ways. -/
structure Q01 where
  num : Nat
  den : Nat
  den_pos : 0 < den
  num_le_den : num ≤ den

namespace Q01

/-- `a ≤ b` as `a.num / a.den ≤ b.num / b.den`, cross-multiplied. -/
def le (a b : Q01) : Prop := a.num * b.den ≤ b.num * a.den

instance decLe (a b : Q01) : Decidable (le a b) :=
  inferInstanceAs (Decidable (a.num * b.den ≤ b.num * a.den))

def zero : Q01 := ⟨0, 1, by decide, by decide⟩
def one : Q01 := ⟨1, 1, by decide, by decide⟩

theorem le_refl (a : Q01) : le a a := Nat.le_refl _
theorem le_total (a b : Q01) : le a b ∨ le b a := Nat.le_total _ _
theorem zero_le (a : Q01) : le zero a := by simp [le, zero]
theorem le_one (a : Q01) : le a one := by simp [le, one]; exact a.num_le_den

/-- Transitivity by cross-multiplication: from `a.n·b.d ≤ b.n·a.d` and
`b.n·c.d ≤ c.n·b.d`, multiply by `c.d` and `a.d` and cancel `b.d > 0`. -/
theorem le_trans {a b c : Q01} (h1 : le a b) (h2 : le b c) : le a c := by
  unfold le at *
  have h1' := Nat.mul_le_mul_right c.den h1
  have h2' := Nat.mul_le_mul_right a.den h2
  have e1 : b.num * a.den * c.den = b.num * c.den * a.den := by
    rw [Nat.mul_assoc, Nat.mul_comm a.den, ← Nat.mul_assoc]
  rw [e1] at h1'
  have h3 := Nat.le_trans h1' h2'
  have e2 : a.num * b.den * c.den = b.den * (a.num * c.den) := by
    rw [Nat.mul_comm a.num, Nat.mul_assoc]
  have e3 : c.num * b.den * a.den = b.den * (c.num * a.den) := by
    rw [Nat.mul_comm c.num, Nat.mul_assoc]
  rw [e2, e3] at h3
  exact Nat.le_of_mul_le_mul_left h3 b.den_pos

instance : Scale Q01 :=
  ⟨le, decLe, zero, one, le_refl, le_trans, le_total, zero_le, le_one⟩

def toString (w : Q01) : String := s!"{w.num}/{w.den}"
instance : Repr Q01 := ⟨fun w _ => Std.Format.text w.toString⟩

end Q01

/-! ### Weighted bases and their cuts -/

variable {α : Type} [DecidableEq α]

/-- A base entry with its holder's weight. -/
structure WEntry (α W : Type) where
  entry : Entry α
  weight : W

/-- A weighted base: a finite list of weighted entries. -/
abbrev WBase (α W : Type) := List (WEntry α W)

/-- The entries of a weighted base, weights forgotten. -/
def WBase.entries (B : WBase α W) : List (Entry α) := B.map (·.entry)

/-- **The cut `B_t`**: the entries weighted `t` or more, for every `t` in the
scale, `zero` included. -/
def cut (B : WBase α W) (t : W) : List (Entry α) :=
  (B.filter (fun e => decide (t ≤ e.weight))).map (·.entry)

/-- `Γ ⇒ Δ` is derivable at threshold `t`: NMMS derivability (the book's
calculus, unchanged) over the cut `B_t`. -/
def DerivableAt (B : WBase α W) (t : W) (Γ Δ : List (Formula α)) : Prop :=
  Derivable (baseRel (cut B t)) Γ Δ

/-- Derivability at a threshold is decidable, by the existing instance over
a pyNMMS base (LeanNmms.Decide). No new proof. -/
instance (B : WBase α W) (t : W) (Γ Δ : List (Formula α)) : Decidable (DerivableAt B t Γ Δ) :=
  inferInstanceAs (Decidable (Derivable (baseRel (cut B t)) Γ Δ))

/-- The decision procedure at a threshold: `fastProve` over the cut. -/
def derivableAt (B : WBase α W) (t : W) (Γ Δ : List (Formula α)) : Bool :=
  fastProve (baseRel (cut B t)) Γ Δ

/-- The procedure is correct at every threshold: `reasoner_correct` over the
cut. Follows from the existing lemma. -/
theorem derivableAt_iff (B : WBase α W) (t : W) (Γ Δ : List (Formula α)) :
    derivableAt B t Γ Δ = true ↔ DerivableAt B t Γ Δ :=
  (reasoner_correct (cut B t) Γ Δ).1

/-! ### Max and min on the scale -/

def maxW (a b : W) : W := if a ≤ b then b else a
def minW (a b : W) : W := if a ≤ b then a else b

/-- The greatest element of a list, `none` for the empty list. -/
def maxList : List W → Option W
  | [] => none
  | t :: l => some (match maxList l with | none => t | some m => maxW t m)

/-- The least element of a list, `none` for the empty list. -/
def minList : List W → Option W
  | [] => none
  | t :: l => some (match minList l with | none => t | some m => minW t m)

/-! ### The degree -/

/-- The candidate thresholds: `zero` and every entry's weight. The sup in
`degree?` is attained at one of these (`cut_theorem`). -/
def candidates (B : WBase α W) : List W := Scale.zero :: B.map (·.weight)

/-- **The degree of `Γ ⇒ Δ`**: the largest candidate threshold at which the
cut derives it; `none` when no cut does, `B_zero` (the whole base) included.
This is `sup { t | B_t ⊢ Γ ⇒ Δ }` by `cut_theorem` and `degree_sup`. -/
def degree? (B : WBase α W) (Γ Δ : List (Formula α)) : Option W :=
  maxList ((candidates B).filter (fun t => derivableAt B t Γ Δ))

/-- "The degree exists and is at least `t`." -/
def DegreeGe (B : WBase α W) (t : W) (Γ Δ : List (Formula α)) : Prop :=
  ∃ d, degree? B Γ Δ = some d ∧ t ≤ d

/-! ### Base monotonicity (new, small) -/

/-- The empty base is `emptyBase`: nothing is derivable over it. -/
theorem derivable_nil {Γ Δ : List (Formula α)} :
    ¬ Derivable (baseRel ([] : List (Entry α))) Γ Δ :=
  emptyBase_underivable

/-- NMMS is monotone in the *base* (not in the premises): a larger base
relation derives everything a smaller one does. Induction on `Derivable`. -/
theorem derivable_mono {R R' : BaseRel α} (h : ∀ X Y, R X Y = true → R' X Y = true)
    {Γ Δ : List (Formula α)} : Derivable R Γ Δ → Derivable R' Γ Δ := by
  sorry

/-- More entries, a larger base relation. -/
theorem baseRel_mono {B1 B2 : List (Entry α)} (h : ∀ e, e ∈ B1 → e ∈ B2) (X Y : List α) :
    baseRel B1 X Y = true → baseRel B2 X Y = true := by
  sorry

/-! ### The cut in `t` -/

/-- **`B_zero` is the whole base**: an entry weighted 0 takes part at
threshold 0. -/
theorem cut_zero (B : WBase α W) : cut B Scale.zero = B.entries := by
  sorry

/-- **Monotonicity of the cut**: a lower threshold keeps every entry a
higher one keeps. -/
theorem cut_antitone {s t : W} (h : s ≤ t) (B : WBase α W) :
    ∀ e, e ∈ cut B t → e ∈ cut B s := by
  sorry

/-- Every cut is part of the base. -/
theorem cut_subset (B : WBase α W) (t : W) : ∀ e, e ∈ cut B t → e ∈ B.entries := by
  sorry

/-- **Monotonicity of derivability in `t`**: derivable at `t` implies
derivable at every `s ≤ t`. Follows from the three lemmas above. -/
theorem derivableAt_antitone {B : WBase α W} {s t : W} (h : s ≤ t)
    {Γ Δ : List (Formula α)} : DerivableAt B t Γ Δ → DerivableAt B s Γ Δ :=
  derivable_mono (fun X Y => baseRel_mono (cut_antitone h B) X Y)

/-- At threshold 0, derivability is the unweighted derivability over all the
entries. Follows from `cut_zero`. -/
theorem derivableAt_zero_iff (B : WBase α W) (Γ Δ : List (Formula α)) :
    DerivableAt B Scale.zero Γ Δ ↔ Derivable (baseRel B.entries) Γ Δ := by
  rw [DerivableAt, cut_zero]

/-! ### The cut theorem and the sup -/

/-- **The cut theorem** (tracer N's first done condition): for every `t` in
the scale, `zero` included, the degree of `Γ ⇒ Δ` is at least `t` exactly
when `Γ ⇒ Δ` is derivable over the entries weighted `t` or more. -/
theorem cut_theorem (B : WBase α W) (t : W) (Γ Δ : List (Formula α)) :
    DegreeGe B t Γ Δ ↔ DerivableAt B t Γ Δ := by
  sorry

/-- No degree exactly when not even the whole base derives the sequent.
Follows from `cut_theorem` at `zero` and `derivableAt_zero_iff`. -/
theorem degree_none_iff (B : WBase α W) (Γ Δ : List (Formula α)) :
    degree? B Γ Δ = none ↔ ¬ Derivable (baseRel B.entries) Γ Δ := by
  sorry

/-- **The degree is the sup, and it is attained**: the sequent is derivable
at its degree, and at no higher threshold. Follows from `cut_theorem`. -/
theorem degree_sup {B : WBase α W} {Γ Δ : List (Formula α)} {d : W}
    (h : degree? B Γ Δ = some d) :
    DerivableAt B d Γ Δ ∧ ∀ t, DerivableAt B t Γ Δ → t ≤ d := by
  sorry

/-- The sup is unique up to the preorder: any other attained maximum
compares equal both ways. Follows from `degree_sup`. -/
theorem degree_sup_unique {B : WBase α W} {Γ Δ : List (Formula α)} {d d' : W}
    (h : degree? B Γ Δ = some d) (hd' : DerivableAt B d' Γ Δ)
    (hmax : ∀ t, DerivableAt B t Γ Δ → t ≤ d') : d ≤ d' ∧ d' ≤ d := by
  sorry

/-- Adding entries never lowers a degree (NMMS is monotone in the base).
Follows from `cut_theorem`, `derivable_mono` and `baseRel_mono`. -/
theorem degree_mono_base {B1 B2 : WBase α W} (h : ∀ e, e ∈ B1 → e ∈ B2)
    {Γ Δ : List (Formula α)} {d : W} (hd : degree? B1 Γ Δ = some d) :
    ∃ d', degree? B2 Γ Δ = some d' ∧ d ≤ d' := by
  sorry

/-! ### Decidability of the degree for finite bases -/

/-- `degree?` is a computable function of a finite base (it is a `def`
built from `fastProve`), so "degree ≥ t" is decidable: by `cut_theorem` it
is the decidable `DerivableAt`. -/
instance decidableDegreeGe (B : WBase α W) (t : W) (Γ Δ : List (Formula α)) :
    Decidable (DegreeGe B t Γ Δ) :=
  decidable_of_iff (DerivableAt B t Γ Δ) (cut_theorem B t Γ Δ).symm

/-! ### The weakest-link property -/

/-- **Weakest link, lower bound**: if some selection `S` of the entries
derives `Γ ⇒ Δ`, the degree is at least the least weight in `S`. -/
theorem weakest_link_lower {B S : WBase α W} (hS : ∀ e, e ∈ S → e ∈ B)
    {m : W} (hm : minList (S.map (·.weight)) = some m)
    {Γ Δ : List (Formula α)} (hd : Derivable (baseRel S.entries) Γ Δ) :
    DegreeGe B m Γ Δ := by
  sorry

/-- **Weakest link, attained**: the degree `d` is the least weight of some
selection of entries that derives the sequent (`cut B d` is one). Together
with `weakest_link_lower`: the degree is the max over derivations of the
min weight used, which is the weakest-link rule. -/
theorem weakest_link_attained {B : WBase α W} {Γ Δ : List (Formula α)} {d : W}
    (h : degree? B Γ Δ = some d) :
    ∃ S : WBase α W, (∀ e, e ∈ S → e ∈ B) ∧ Derivable (baseRel S.entries) Γ Δ ∧
      ∃ m, minList (S.map (·.weight)) = some m ∧ d ≤ m := by
  sorry

/-! ### Agreement with the unweighted NMMS when every weight is 1 -/

/-- An unweighted base, every entry weighted `one`. -/
def lift (B : List (Entry α)) : WBase α W := B.map (fun e => ⟨e, Scale.one⟩)

theorem lift_entries (B : List (Entry α)) : (lift (W := W) B).entries = B := by
  sorry

/-- Every cut of an all-ones base is the whole base (`le_one`). -/
theorem cut_lift (B : List (Entry α)) (t : W) : cut (lift B) t = B := by
  sorry

/-- At every threshold, derivability over the all-ones base is the book's
derivability over the unweighted base. Follows from `cut_lift`. -/
theorem derivableAt_lift (B : List (Entry α)) (t : W) (Γ Δ : List (Formula α)) :
    DerivableAt (lift B) t Γ Δ ↔ Derivable (baseRel B) Γ Δ := by
  rw [DerivableAt, cut_lift]

/-- **Agreement with NMMS**: over the all-ones base the degree is `one` for
exactly the derivable sequents and `none` for the rest. -/
theorem degree_lift (B : List (Entry α)) (Γ Δ : List (Formula α)) :
    degree? (lift (W := W) B) Γ Δ =
      (if fastProve (baseRel B) Γ Δ then some Scale.one else none) := by
  sorry

/-! ### A source's own uncertainty, combined with the holder's weight -/

/-- The possibilistic combination: the holder's weight on a claim from a
source that is itself `source` sure is the `min` of the two. The source's
supplied value stays a preserved record elsewhere; this is only the
effective weight. -/
def combine (holder source : W) : W := minW holder source

theorem combine_le_holder (holder source : W) : combine holder source ≤ holder := by
  sorry

theorem combine_le_source (holder source : W) : combine holder source ≤ source := by
  sorry

/-- A source that is fully sure leaves the holder's weight as it is. -/
theorem combine_one (holder : W) : combine holder Scale.one = holder := by
  simp [combine, minW, le_one]

end Possibilistic
end NMMS
