import TCSlib.Cryptography.ZeroKnowledge.LevinHardness
open Lean Meta Elab Command
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mine (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => (mods[i.toNat]!).toString.startsWith "TCSlib.Cryptography.ZeroKnowledge.LevinHardness"
    | none => false
  let mut out := #[]
  let mut nonstd := 0
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if mine n && !isPrivateName n && !n.isInternalDetail && !(isAuxRecursor env n || isNoConfusion env n) then
      count := count + 1
      let axs ← liftCoreM (Lean.collectAxioms n)
      let std := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
      if !std then nonstd := nonstd + 1
      let ty ← liftTermElabM (do let f ← ppExpr ci.type; pure (toString f))
      out := out.push s!"{n}\t{if std then "STD" else "NONSTD"}\t{axs.toList}\n  : {ty.replace "\n" " "}"
  IO.FS.writeFile "/home/user/work/ev/evidence/axioms/stmtdump.txt" (String.intercalate "\n" (out.qsort (· < ·)).toList ++ "\n")
  logInfo m!"public constants: {count}, non-standard axioms: {nonstd}"
