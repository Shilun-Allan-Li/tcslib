import TCSlib.Complexity.BranchingPrograms.BarringtonConverse
open Lean Meta Elab Command

/-- Admitted constants (whose own body mentions `sorryAx`) reachable from `n`. -/
partial def sorryRoots (env : Environment) (n : Name) : StateM (NameSet × NameSet) Unit := do
  let (vis, roots) ← get
  if vis.contains n then return
  set (vis.insert n, roots)
  let some ci := env.find? n | return
  let deps := ci.getUsedConstantsAsSet
  if deps.contains ``sorryAx then modify fun (v, r) => (v, r.insert n)
  for d in deps do sorryRoots env d

elab "#sorry_trace " id:ident : command => do
  let env ← getEnv
  let n := id.getId
  let ((), (_, roots)) := (sorryRoots env n).run ({}, {})
  logInfo m!"{n}: {roots.toList}"

#sorry_trace BranchingProgram.Instr.wire_eval
#sorry_trace BranchingProgram.Instr.depth_wire_le
#sorry_trace BranchingProgram.Instr.maxFanin_wire_le
#sorry_trace BranchingProgram.wireComp_eval
#sorry_trace BranchingProgram.depth_wireComp_le
#sorry_trace BranchingProgram.compTree_eval
#sorry_trace BranchingProgram.depth_compTree_le
#sorry_trace BranchingProgram.maxFanin_compTree_le
#sorry_trace BranchingProgram.toFormula_eval
#sorry_trace BranchingProgram.depth_toFormula_le
#sorry_trace BranchingProgram.maxFanin_toFormula_le
