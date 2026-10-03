import PrimalitySheafVerification.BuildAll

/-! Whole-project axiom audit: for every constant defined in a `PrimalitySheafVerification.*`
module, compute (memoized, iterative DFS over `getUsedConstantsAsSet`) whether its transitive
dependencies reach any axiom other than `propext`, `Classical.choice`, `Quot.sound`. -/

open Lean Elab Command

def auditTaint (env : Environment) (roots : Array Name) : Std.HashMap Name (Option Name) := Id.run do
  let allowed : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound
  let mut status : Std.HashMap Name (Option Name) := {}
  let mut expanded : NameSet := {}
  let mut stack : Array (Name × Bool) := roots.map (·, false)
  while !stack.isEmpty do
    let (c, done) := stack.back!
    stack := stack.pop
    if status.contains c then continue
    match env.find? c with
    | none => status := status.insert c none
    | some ci =>
      match ci with
      | .axiomInfo _ => status := status.insert c (if allowed.contains c then none else some c)
      | _ =>
        let deps := ci.getUsedConstantsAsSet.toArray
        if !done then
          if expanded.contains c then continue  -- cycle guard
          expanded := expanded.insert c
          stack := stack.push (c, true)
          for d in deps do
            if !status.contains d then stack := stack.push (d, false)
        else
          let mut w : Option Name := none
          for d in deps do
            if w.isNone then w := (status.getD d none)
          status := status.insert c w
  return status

elab "#audit_psv_axioms" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut roots : Array Name := #[]
  for (c, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? c then
      if (`PrimalitySheafVerification).isPrefixOf mods[idx.toNat]! then
        roots := roots.push c
  let st := auditTaint env roots
  let mut bad : Array (Name × Name) := #[]
  let mut perAxiom : Std.HashMap Name Nat := {}
  for c in roots do
    if let some (some a) := st.get? c then
      bad := bad.push (c, a)
      perAxiom := perAxiom.insert a (perAxiom.getD a 0 + 1)
  logInfo m!"PSV constants audited: {roots.size}; tainted by non-standard axioms: {bad.size}; by axiom: {perAxiom.toList}; first 30: {(bad.toList.take 30)}"

#audit_psv_axioms

/-! Sanity check that the auditor detects taint: a deliberately `sorry`-proved canary must be
reported as depending on `sorryAx`, and a clean Mathlib lemma must not. -/
theorem auditCanary : (1 : ℕ) = 2 := sorry

elab "#audit_canary" : command => do
  let st := auditTaint (← getEnv) #[``auditCanary, ``Nat.add_comm]
  logInfo m!"canary: {st.get? ``auditCanary}; control Nat.add_comm: {st.get? ``Nat.add_comm}"

#audit_canary
