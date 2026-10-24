/-
  LeanNmms.Weakening

  The book's counterexample to Weakening (Hlobil and Brandom 2025, ch. 3): a
  base containing `p |~ q` but not `p, r |~ q`. With pyNMMS's EXACT policy
  (the default) the base entry licenses only `p ⇒ q` itself, so adding `r` to
  the premises loses the implication. Atoms are `Nat` (p = 0, q = 1, r = 2) so
  that the decision procedure runs in the kernel (`decide`); its verdicts are
  trusted because of `fastProve_iff`.

  For contrast, the same entry with pyNMMS's MONOTONE policy survives the
  addition, and with a GUARDED policy whose defeater is `r` it does not.
-/
import LeanNmms.Base
import LeanNmms.Decide

namespace NMMS

open Formula

/-- The base `{p |~ q}` with the given policy. -/
def pq (rob : Robustness Nat) : List (Entry Nat) := [{ ant := [0], con := [1], rob := rob }]

theorem pq_exact_derives : Derivable (baseRel (pq .exact)) [atom 0] [atom 1] := by
  decide

theorem pq_exact_not_weakened :
    ¬ Derivable (baseRel (pq .exact)) [atom 0, atom 2] [atom 1] := by
  decide

/-- **Weakening fails** in NMMS (over a pyNMMS base). -/
theorem weakening_fails :
    ∃ (R : BaseRel Nat) (Γ Δ : List (Formula Nat)) (φ : Formula Nat),
      Derivable R Γ Δ ∧ ¬ Derivable R (φ :: Γ) Δ :=
  ⟨baseRel (pq .exact), [atom 0], [atom 1], atom 2, pq_exact_derives, by
    intro h
    exact pq_exact_not_weakened (derivable_congr_base _ h
      (fun x => by simp [or_comm]) (fun _ => Iff.rfl))⟩

/-- Weakening also fails with a complex sentence added: `p, ¬r ⇒ q` is lost. -/
theorem pq_exact_not_weakened_neg :
    ¬ Derivable (baseRel (pq .exact)) [atom 0, neg (atom 2)] [atom 1] := by
  decide

/-- MONOTONE keeps the implication under the addition. -/
theorem pq_monotone_weakened :
    Derivable (baseRel (pq .monotone)) [atom 0, atom 2] [atom 1] := by
  decide

/-- GUARDED with defeater `r` loses it, and keeps it under other additions. -/
theorem pq_guarded :
    ¬ Derivable (baseRel (pq (.guarded { left := [2] }))) [atom 0, atom 2] [atom 1] ∧
    Derivable (baseRel (pq (.guarded { left := [2] }))) [atom 0, atom 3] [atom 1] := by
  decide

/-- No Containment is added: over the empty base `p ⇒ p` is not derivable. -/
theorem empty_base_no_identity : ¬ Derivable (baseRel ([] : List (Entry Nat))) [atom 0] [atom 0] := by
  decide

/-- Excluded middle needs the base to supply `r |~ r`: over `{p |~ q}` it is
not derivable (R∨, then R¬, leave `r ⇒ r`, which is not in the base). -/
theorem excluded_middle_not_derived :
    ¬ Derivable (baseRel (pq .exact)) [] [disj (atom 2) (neg (atom 2))] := by
  decide

/-- With `r |~ r` supplied (MONOTONE, so it holds in any context), excluded
middle for `r` is derivable. -/
theorem excluded_middle_with_rr :
    Derivable (baseRel (pq .exact ++ [{ ant := [2], con := [2], rob := .monotone }])) []
      [disj (atom 2) (neg (atom 2))] := by
  decide

end NMMS
