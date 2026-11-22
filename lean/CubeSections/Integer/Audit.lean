import CubeSections.Integer.Balanced
import CubeSections.Integer.Window
import CubeSections.Integer.GramPacking
import Lean.Util.CollectAxioms

/-! Exhaustive theorem-signature and transitive-axiom audit of imported project declarations. -/
set_option pp.universes true
set_option pp.fullNames true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    if info.isTheorem && (`CubeSections).isPrefixOf name then some name else none
  let names := names.toArray.qsort Name.lt
  for name in names do
    let axioms ← collectAxioms name
    for a in axioms do
      unless a == `propext || a == `Classical.choice || a == `Quot.sound do
        throwError "Unapproved transitive dependency {a} in {name}"
    elabCommand (← `(#print sig $(mkIdent name)))
    elabCommand (← `(#print axioms $(mkIdent name)))
  logInfo m!"MSC_AUDIT_ACCEPTED_THEOREMS={names.size}"
