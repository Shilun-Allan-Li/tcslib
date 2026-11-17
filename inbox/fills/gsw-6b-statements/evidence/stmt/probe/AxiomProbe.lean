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
open Lean Elab Command

/-! Axiom census and `sorryAx` dependency trace (gsw-6b-statements; adapted from the 6a statement
job's `AxiomProbe.lean`). For every constant of the new and changed modules: its axioms
(`Lean.collectAxioms`). For every constant whose axioms include `sorryAx`: the admitted
declarations through which it reaches `sorryAx`, found by walking its dependency closure inside
TCSlib modules and stopping at each constant whose own type or value mentions `sorryAx`
directly (an admitted declaration). Change against 6a: the walk crosses all TCSlib modules (6b
reaches `sorryAx` through 6a's admitted declarations), and each `via` entry names its module. -/

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
  let names := env.header.moduleNames
  let idxs := mods.filterMap env.getModuleIdx?
  let inMods (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => idxs.contains i | none => false
  let inTCSlib (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => (`TCSlib).isPrefixOf names[i.toNat]! | none => false
  let modOf (n : Name) : String := match env.getModuleIdxFor? n with
    | some i => toString names[i.toNat]! | none => "?"
  let directSorry (n : Name) : Bool := match env.find? n with
    | some c =>
      let v := (c.value? (allowOpaque := true)).getD (mkConst `True)
      (c.type.getUsedConstants ++ v.getUsedConstants).contains ``sorryAx
    | none => false
  let mut out : Array String := #[]
  for (n, c) in env.constants.toList do
    if inMods n then
      let axs ← liftCoreM (Lean.collectAxioms n)
      let tag := if n.isInternal then "AUX" else "DECL"
      let axl := axs.qsort (·.toString < ·.toString) |>.toList
      out := out.push s!"{tag}\t{modOf n}\t{n}\t{axl}"
      if axs.contains ``sorryAx then
        let mut seen : Std.HashSet Name := {}
        let mut stack : Array Name := #[n]
        let mut via : Array String := #[]
        while !stack.isEmpty do
          let m := stack.back!
          stack := stack.pop
          if seen.contains m then continue
          seen := seen.insert m
          if directSorry m then
            via := via.push s!"{m}@{modOf m}"
            continue
          let some cm := env.find? m | continue
          let v := (cm.value? (allowOpaque := true)).getD (mkConst `True)
          for d in cm.type.getUsedConstants ++ v.getUsedConstants do
            if inTCSlib d && !seen.contains d then stack := stack.push d
        let vl := via.qsort (· < ·) |>.toList
        out := out.push s!"TRACE\t{n}\tvia {vl}"
  for l in out.qsort (· < ·) do
    IO.println l
