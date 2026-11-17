import TCSlib.Cryptography.LWE.BitEncoding
import TCSlib.Cryptography.LWE.Ratio
import TCSlib.Cryptography.LWE
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Asymptotic
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Lean Elab Command Meta

/-! Statement dump (gsw-6b-statements; adapted from the 6a statement job's `StmtDump.lean`): every
non-internal constant of the new and changed modules, with its kind, module and type printed
with full names, and the TCSlib constants its type mentions. -/

set_option pp.fullNames true in
set_option pp.funBinderTypes true in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : List Name := [
    `TCSlib.Cryptography.LWE.BitEncoding,
    `TCSlib.Cryptography.LWE.Ratio,
    `TCSlib.Cryptography.LWE,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Asymptotic,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW]
  let idxs := mods.filterMap env.getModuleIdx?
  let names := env.header.moduleNames
  let mut out : Array (String × String) := #[]
  for (n, c) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    if idxs.contains i && !n.isInternal then
      let fmt ← liftTermElabM <| ppExpr c.type
      let consts := c.type.getUsedConstants.filter fun d =>
        (`TCSlib).isPrefixOf d || (`BoolCircuit).isPrefixOf d || (`BranchingProgram).isPrefixOf d ||
          (`Complexity).isPrefixOf d
      let kind := match c with
        | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor" | .recInfo _ => "recursor" | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
      out := out.push (n.toString, s!"{n}\t{kind}\t{names[i.toNat]!}\n  : {fmt}\n  CONSTS {consts.toList}")
  for (_, s) in out.qsort (fun a b => a.1 < b.1) do
    IO.println s
