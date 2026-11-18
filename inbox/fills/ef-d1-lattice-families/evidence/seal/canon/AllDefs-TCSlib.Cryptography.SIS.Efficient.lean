import TCSlib.Cryptography.SIS.Efficient
/-! Canonical seal candidates for TCSlib.Cryptography.SIS.Efficient: every ordinary TCSlib definition of the full import closure
defined in another module. Columns: name, kind (def | instance | reducible | matcher), module. -/
open Lean Meta in
run_cmd do
  let env ← getEnv
  let some me := env.getModuleIdx? `TCSlib.Cryptography.SIS.Efficient | throwError "no module"
  let mods := env.header.moduleNames
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    if idx == me then continue
    let modN := mods[idx.toNat]!
    if modN.getRoot != `TCSlib then continue
    let .defnInfo _ := ci | continue
    if isPrivateName n then continue
    if n.isInternal then continue
    if n.hasNum then continue
    if isAuxRecursor env n || isNoConfusion env n || env.isProjectionFn n then continue
    let s := n.toString
    if s.endsWith ".eq_def" || s.endsWith ".eq_unfold" then continue
    if (n.components.getLast!.toString.startsWith "eq_") then continue
    if (n.components.getLast!.toString.startsWith "proof_") then continue
    let kind :=
      if isMatcherCore env n then "matcher"
      else if isInstanceCore env n then "instance"
      else if getReducibilityStatusCore env n == .reducible then "reducible"
      else if getReducibilityStatusCore env n == .irreducible then "irreducible"
      else "def"
    out := out.push s!"{s}\t{kind}\t{modN}"
  IO.FS.writeFile "/home/user/work/evidence/seal/canon/TCSlib.Cryptography.SIS.Efficient.all.tsv" (String.intercalate "\n" out.qsort.toList ++ "\n")
