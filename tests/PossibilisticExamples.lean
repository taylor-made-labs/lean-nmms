/-
  tests/PossibilisticExamples.lean — tracer N: the computed degree on the
  same cases the Python tests in graph-nmms use (tests/test_possibilistic.py).

  `#eval` lines are evidence, not proofs; the `example ... := by decide`
  lines are kernel-checked computations of `derivableAt` and `degree?`.
  Run: `lake env lean tests/PossibilisticExamples.lean`.
-/
import LeanNmms.Possibilistic

open NMMS NMMS.Possibilistic Formula

/-- A rational weight `n/d` in [0,1], with its side conditions decided. -/
def w (n d : Nat) (h1 : 0 < d := by decide) (h2 : n ≤ d := by decide) : Q01 := ⟨n, d, h1, h2⟩

/-- The example base of the Python tests: `p |~ q` at 1, `p |~ r` at 1/2,
`p |~ q, r` at 1/2, and `r |~ s` at 0. -/
def ex : WBase String Q01 :=
  [⟨{ ant := ["p"], con := ["q"] }, w 1 1⟩,
   ⟨{ ant := ["p"], con := ["r"] }, w 1 2⟩,
   ⟨{ ant := ["p"], con := ["q", "r"] }, w 1 2⟩,
   ⟨{ ant := ["r"], con := ["s"] }, w 0 1⟩]

-- degree(p ⇒ q ∧ r) = 1/2: R∧ needs p ⇒ q, p ⇒ r and p ⇒ q, r; the weakest is 1/2.
#eval degree? ex [atom "p"] [conj (atom "q") (atom "r")]
-- degree(p ⇒ q) = 1
#eval degree? ex [atom "p"] [atom "q"]
-- degree(r ⇒ s) = 0: derivable over B_0 only, which is not "none".
#eval degree? ex [atom "r"] [atom "s"]
-- degree(q ⇒ p) = none: no cut derives it.
#eval degree? ex [atom "q"] [atom "p"]

example : derivableAt ex (w 1 2) [atom "p"] [conj (atom "q") (atom "r")] = true := by decide
example : derivableAt ex (w 3 4) [atom "p"] [conj (atom "q") (atom "r")] = false := by decide
example : derivableAt ex (w 0 1) [atom "r"] [atom "s"] = true := by decide
example : derivableAt ex (w 1 4) [atom "r"] [atom "s"] = false := by decide

-- The empty weighted base derives nothing at any threshold.
example : derivableAt ([] : WBase String Q01) (w 0 1) [atom "p"] [atom "p"] = false := by decide
#eval degree? ([] : WBase String Q01) [atom "p"] [atom "p"]

-- Agreement with the unweighted base: every weight 1.
def plain : List (Entry String) := [{ ant := ["p"], con := ["q"] }]
#eval degree? (lift (W := Q01) plain) [atom "p"] [atom "q"]
#eval degree? (lift (W := Q01) plain) [atom "q"] [atom "p"]

-- The source combination is min.
#eval combine (w 4 5) (w 1 2)
#eval combine (w 4 5) Q01.one
