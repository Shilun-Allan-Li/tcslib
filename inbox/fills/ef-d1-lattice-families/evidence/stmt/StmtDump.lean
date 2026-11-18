import TCSlib.Cryptography.LWE.Efficient
import TCSlib.Cryptography.SIS.Efficient
/-! StmtDump + axiom probe (evidence only): every new public constant of the two new modules, with
its full name, kind and type, and the axioms it depends on (`Lean.collectAxioms`). -/
open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  let targets := #[`TCSlib.Cryptography.LWE.Efficient, `TCSlib.Cryptography.SIS.Efficient]
  let mut lines : Array String := #[]
  let mut ax : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modN := env.header.moduleNames[idx.toNat]!
    unless targets.contains modN do continue
    if isPrivateName n || n.isInternal || n.hasNum then continue
    if isAuxRecursor env n || isNoConfusion env n then continue
    let kind := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .inductInfo _ => "structure"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .axiomInfo _ => "AXIOM"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
    let ty ← liftTermElabM <| ppExpr ci.type
    lines := lines.push s!"{modN}\t{kind}\t{n}\t{(toString ty).replace "\n" " "}"
    let axs ← liftTermElabM <| (Lean.collectAxioms n : MetaM (Array Name))
    ax := ax.push s!"{n}\t{(axs.qsort (·.toString < ·.toString)).toList}"
  IO.FS.writeFile "/home/user/work/evidence/stmt/stmtdump.tsv"
    (String.intercalate "\n" (lines.qsort (· < ·)).toList ++ "\n")
  IO.FS.writeFile "/home/user/work/evidence/stmt/axioms.tsv"
    (String.intercalate "\n" (ax.qsort (· < ·)).toList ++ "\n")
