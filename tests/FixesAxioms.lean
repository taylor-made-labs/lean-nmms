/- Enumerate every project constant, not only a hand-picked theorem list. -/
import Lean
import Main
import LeanNmms.Derivation
import LeanNmms.Ground
import LeanNmms.Entitlement

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0 -- Eval fix (21 Oct, hub): type annotation for Lean 4.34.1
  for (name, _) in env.constants.toList do
    -- Also audit Main's parser/dispatcher and private/nested declarations.
    let project := match env.getModuleIdxFor? name with
      | some idx =>
        let mod := env.header.moduleNames[idx.toNat]!
        mod == `Main || mod == `LeanNmms || (`LeanNmms).isPrefixOf mod
      | none => false
    if project then
      checked := checked + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "disallowed axiom {ax} in {name}"
  if checked == 0 then throwError "no project constants audited"
  logInfo m!"FIXES_AXIOMS_OK {checked} constants"
