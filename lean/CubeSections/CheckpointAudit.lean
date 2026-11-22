import CubeSections
import Lean.Util.CollectAxioms

/-! Full project theorem-signature and transitive-dependency audit. -/
set_option pp.universes true
set_option pp.fullNames true

example : CubeSections.AttainmentStatement := CubeSections.balancedSectionAttains

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    if info.isTheorem && (`CubeSections).isPrefixOf name then some name else none
  let names := names.toArray.qsort Name.lt
  for name in names do
    let deps ← collectAxioms name
    for a in deps do
      unless a == `propext || a == `Classical.choice || a == `Quot.sound do
        throwError "Unapproved transitive dependency {a} in {name}"
    elabCommand (← `(#print sig $(mkIdent name)))
    elabCommand (← `(#print axioms $(mkIdent name)))
  logInfo m!"MSC_AUDIT_ACCEPTED_THEOREMS={names.size}"
