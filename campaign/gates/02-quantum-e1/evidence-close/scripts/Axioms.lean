import TCSlib.Quantum
import TCSlib.Complexity.Promise
import TCSlib.Complexity.Counting
import Lean.Util.CollectAxioms

/-! Axiom census for the quantum-phase1 gate: for every non-internal constant declared in a
module under audit, print its axioms. Run with `lean`, LEAN_PATH set as in
`scripts/lean_check_tree.sh`. -/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : Array Name := env.header.moduleNames
  let audited (m : Name) : Bool :=
    (`TCSlib.Quantum).isPrefixOf m || (`TCSlib.Complexity.Promise).isPrefixOf m ||
      (`TCSlib.Complexity.Counting).isPrefixOf m
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if n.isInternal then continue
    match env.getModuleIdxFor? n with
    | none => continue
    | some idx =>
      let m := mods[idx.toNat]!
      if !audited m then continue
      let axs ← liftCoreM <| Lean.collectAxioms n
      let tag := if axs.contains ``sorryAx then "SORRY" else "CLEAN"
      let axStr := ", ".intercalate (axs.toList.map toString |>.mergeSort)
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
        | .recInfo _ => "recursor" | .quotInfo _ => "quot"
      rows := rows.push s!"{tag}\t{kind}\t{m}\t{n}\t[{axStr}]"
  for r in rows.qsort (· < ·) do
    IO.println r
