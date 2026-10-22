/- Fix 3 kernel examples for ground closure and the entitlement least fixpoint. -/
import LeanNmms.Ground
import LeanNmms.Entitlement

open NMMS

namespace FixesGroundTests

def rules : List GroundRule := [
  { name := "seed-mid", layer := 1, premises := ["seed"],
    conclusion := some "mid", defeaters := [] },
  { name := "mid-ready", layer := 2, premises := ["mid"],
    conclusion := some "ready", defeaters := [["blocked"]] }]

def good : GroundClosureCert := {
  applications := [
    { entry := 0, layer := 1, defeaterChecks := [] },
    { entry := 1, layer := 2, defeaterChecks := [true] }],
  closure := ["seed", "mid", "ready"] }

example : checkGroundClosure rules ["seed"] good = true := by decide
example : checkGroundClosure rules ["seed", "blocked"]
    { applications := [{ entry := 0, layer := 1, defeaterChecks := [] }],
      closure := ["seed", "blocked", "mid"] } = true := by decide
example : checkGroundClosure rules ["seed"]
    { good with applications := [
      { entry := 0, layer := 1, defeaterChecks := [] },
      { entry := 1, layer := 2, defeaterChecks := [] }] } = false := by decide
example : checkGroundClosure rules ["seed"]
    { good with applications := [
      { entry := 0, layer := 1, defeaterChecks := [] },
      { entry := 1, layer := 9, defeaterChecks := [true] }] } = false := by decide
example : checkGroundClosure rules ["seed", "blocked"]
    { good with closure := ["seed", "blocked", "mid", "ready"] } = false := by decide
example : checkGroundClosure rules ["seed"]
    { good with closure := ["seed", "mid"] } = false := by decide
example : checkGroundClosure rules ["seed"]
    { good with closure := ["seed", "mid", "ready", "invented"] } = false := by decide
example : checkGroundClosure rules [] good = false := by decide
example : checkGroundClosure rules ["seed"]
    { good with applications := good.applications.reverse } = false := by decide

-- A lower stratum can derive a defeater; it must be visible to the next layer.
def layered : List GroundRule := [
  { name := "block", layer := 0, premises := ["seed"],
    conclusion := some "blocked", defeaters := [] }] ++ rules
example : checkGroundClosure layered ["seed"] {
  applications := [
    { entry := 0, layer := 0, defeaterChecks := [] },
    { entry := 1, layer := 1, defeaterChecks := [] }],
  closure := ["seed", "blocked", "mid"] } = true := by decide

def nodes : List EntitlementNode := [
  { holder := "agent:amber", claim := "seed", defaultOK := true, blocked := false, supports := [] },
  { holder := "agent:amber", claim := "mid", defaultOK := false, blocked := false, supports := [[0]] },
  { holder := "agent:amber", claim := "ready", defaultOK := false, blocked := false, supports := [[1]] },
  { holder := "agent:teal", claim := "ready", defaultOK := false, blocked := false, supports := [] },
  { holder := "agent:amber", claim := "cycle-a", defaultOK := false, blocked := false, supports := [[5]] },
  { holder := "agent:teal", claim := "cycle-b", defaultOK := false, blocked := false, supports := [[4]] },
  { holder := "agent:amber", claim := "conflicted", defaultOK := true, blocked := true, supports := [] }]

def rounds : List (List Nat) := [[], [0], [0, 1], [0, 1, 2]]
example : checkEntitlement nodes rounds = true := by decide
-- Unsupported entitlement, attribution transfer, an unseeded deferral cycle,
-- conflict, a merely sound but incomplete prefix, and a skipped round.
example : checkEntitlement nodes (rounds ++ [[0, 1, 2, 3]]) = false := by decide
example : checkEntitlement nodes [[], [0], [0, 1], [0, 1, 3]] = false := by decide
example : checkEntitlement nodes (rounds ++ [[0, 1, 2, 4, 5]]) = false := by decide
example : checkEntitlement nodes (rounds ++ [[0, 1, 2, 6]]) = false := by decide
example : checkEntitlement nodes [[], [0]] = false := by decide
example : checkEntitlement nodes [[], [0, 1, 2]] = false := by decide

example (cert : GroundClosureCert)
    (h : checkGroundClosure rules ["seed"] cert = true) :
    ∀ atom ∈ cert.closure, GroundClosure rules ["seed"] atom :=
  checkGroundClosure_sound h
example (rs : List (List Nat)) (h : checkEntitlement nodes rs = true) :
    EntitlementExact nodes rs := checkEntitlement_sound h

end FixesGroundTests
