import TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators
import TCSlib.Complexity.CircuitComplexity.FormulaArith
import TCSlib.Complexity.CircuitComplexity.TreeNCAC
open Lean Elab Command

/-! Axiom census and `sorryAx` dependency trace (6a statement job) of the new and changed modules. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : List Name := [
    `TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators,
    `TCSlib.Complexity.CircuitComplexity.FormulaArith,
    `TCSlib.Complexity.CircuitComplexity.TreeNCAC]
  let names := env.header.moduleNames
  let idxs := mods.filterMap env.getModuleIdx?
  let inMods (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => idxs.contains i | none => false
  -- constants of the modules whose own type or value mentions `sorryAx` directly
  let mut direct : Std.HashSet Name := {}
  for (n, c) in env.constants.toList do
    if inMods n then
      let v := (c.value? (allowOpaque := true)).getD (mkConst `True)
      if (c.type.getUsedConstants ++ v.getUsedConstants).contains ``sorryAx then
        direct := direct.insert n
  let mut out : Array String := #[]
  for (n, c) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    if idxs.contains i then
      let axs ← liftCoreM (Lean.collectAxioms n)
      let tag := if n.isInternal then "AUX" else "DECL"
      let axl := axs.qsort (·.toString < ·.toString) |>.toList
      out := out.push s!"{tag}\t{names[i.toNat]!}\t{n}\t{axl}"
      if axs.contains ``sorryAx then
        -- walk the closure inside the modules
        let mut seen : Std.HashSet Name := {}
        let mut stack : Array Name := #[n]
        let mut via : Array Name := #[]
        while !stack.isEmpty do
          let m := stack.back!
          stack := stack.pop
          if seen.contains m then continue
          seen := seen.insert m
          if direct.contains m then via := via.push m
          let some cm := env.find? m | continue
          let v := (cm.value? (allowOpaque := true)).getD (mkConst `True)
          for d in cm.type.getUsedConstants ++ v.getUsedConstants do
            if inMods d && !seen.contains d then stack := stack.push d
        let vl := via.qsort (·.toString < ·.toString) |>.toList
        out := out.push s!"TRACE\t{n}\tvia {vl}"
  for l in out.qsort (· < ·) do
    IO.println l
