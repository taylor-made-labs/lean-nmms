/- Audit every production declaration, including private/generated declarations.
   Read types and bodies from the checked environment instead of trusting the
   serialized axiom summaries used by `collectAxioms` for imported modules.

   One traversal of the dependency union checks every root without repeatedly
   visiting shared dependencies. This checks allowed assumptions; it does not
   replay kernel checking. CI runs `leanchecker` separately for that purpose. -/
import Lean
import LeanNmms
import Main

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let checkedEnv := env.checked.get
  let mut roots : Array Name := #[]
  let mut hasMain := false
  let mut hasLibrary := false
  for (name, _) in env.constants.toList do
    -- Select by originating module, not declaration namespace: Main has root
    -- declarations, and Lean also generates private and nested names.
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      let isMain := mod == `Main
      let isLibrary := mod == `LeanNmms || (`LeanNmms).isPrefixOf mod
      if isMain || isLibrary then
        roots := roots.push name
        hasMain := hasMain || isMain
        hasLibrary := hasLibrary || isLibrary
  if roots.isEmpty then throwError "no production declarations selected"
  if !hasMain || !hasLibrary then
    throwError "missing production roots: Main={hasMain}, LeanNmms={hasLibrary}"

  let mut pending := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let expressions ← match checkedEnv.find? name with
      | some (.axiomInfo v) =>
        axioms := axioms.insert name
        pure #[v.type]
      | some (.defnInfo v) => pure #[v.type, v.value]
      | some (.thmInfo v) => pure #[v.type, v.value]
      | some (.opaqueInfo v) => pure #[v.type, v.value]
      | some (.quotInfo _) => pure #[]
      | some (.ctorInfo v) => pure #[v.type]
      | some (.recInfo v) => pure #[v.type]
      | some (.inductInfo v) =>
        pending := pending ++ v.ctors.toArray
        pure #[v.type]
      | none => throwError "missing checked-environment declaration: {name}"
    for expression in expressions do
      pending := pending ++ expression.getUsedConstants

  let found := axioms.toArray.qsort Name.lt
  for ax in found do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "disallowed reachable axiom {ax}"
  -- Keep the marker consumed by CI and the Python test. The count is dynamic,
  -- so adding legitimate production declarations does not require updating it.
  logInfo m!"FIXES_AXIOMS_OK {roots.size} constants; {seen.size} reachable declarations; axioms={found}"
