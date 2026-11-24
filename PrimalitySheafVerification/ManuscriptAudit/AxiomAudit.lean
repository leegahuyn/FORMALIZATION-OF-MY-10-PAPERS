import Lean
import PrimalitySheafVerification.BuildAll

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let prefix := "PrimalitySheafVerification."
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut counts : Std.HashMap Name Nat := {}
  let mut flagged := 0
  liftIO <| IO.println "kind\tmodule\tdeclaration\taxioms\tunexpected"
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if let some modName := moduleNames[idx.toNat]? then
        if modName.toString.startsWith prefix then
          let axioms ← collectAxioms name
          let unexpected := axioms.filter fun axiomName => !allowed.contains axiomName
          let listed := String.intercalate "," (axioms.toList.map Name.toString)
          let extra := String.intercalate "," (unexpected.toList.map Name.toString)
          liftIO <| IO.println s!"declaration\t{modName}\t{name}\t{listed}\t{extra}"
          counts := counts.insert modName ((counts[modName]?).getD 0 + 1)
          if !unexpected.isEmpty then
            flagged := flagged + 1
  for modName in moduleNames do
    if modName.toString.startsWith prefix then
      liftIO <| IO.println s!"module-count\t{modName}\t{(counts[modName]?).getD 0}"
  if counts.isEmpty then
    throwError "No project declarations were found."
  if flagged > 0 then
    throwError "{flagged} declarations depend on an axiom outside the audit allowlist. See the unexpected column."
