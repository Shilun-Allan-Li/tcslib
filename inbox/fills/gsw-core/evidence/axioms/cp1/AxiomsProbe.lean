import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Gadget
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Eval
import Lean

/-!
Axioms and dependency trace for the gsw-core fill (probe, not library code).

For every constant stored by the five owned modules (theorems, definitions, auxiliary
declarations, including private and compiler-generated ones), print its axioms
(`Lean.collectAxioms`) and walk its constant closure, listing every constant in the closure
whose own value or type mentions `sorryAx` directly (the sorried constants it reaches).
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mods : Array Name := #[
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Gadget,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric,
    `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Eval]
  let direct (ci : ConstantInfo) : Bool :=
    ci.type.getUsedConstants.contains ``sorryAx ||
      (ci.value?.map (·.getUsedConstants.contains ``sorryAx)).getD false
  let mut names : Array (Name × Name) := #[]
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if mods.contains m then names := names.push (m, n)
  names := names.qsort (fun a b => a.1.lt b.1 || (a.1 == b.1 && a.2.lt b.2))
  let mut total := 0
  let mut withSorry := 0
  for (m, n) in names do
    total := total + 1
    let axs ← Lean.collectAxioms n
    let axs := axs.qsort Name.lt
    -- dependency closure
    let mut seen : NameSet := {}
    let mut stack : Array Name := #[n]
    let mut sorried : Array Name := #[]
    while h : stack.size > 0 do
      let c := stack.back
      stack := stack.pop
      if seen.contains c then continue
      seen := seen.insert c
      if let some ci := env.find? c then
        if direct ci then sorried := sorried.push c
        for d in ci.type.getUsedConstants do stack := stack.push d
        if let some v := ci.value? then
          for d in v.getUsedConstants do stack := stack.push d
    if axs.contains ``sorryAx then withSorry := withSorry + 1
    logInfo m!"GSWCORE-AXIOMS {m} {n} axioms={axs.toList} closure={seen.size} sorried={(sorried.qsort Name.lt).toList}"
  logInfo m!"GSWCORE-AXIOMS-SUMMARY constants={total} reaching_sorryAx={withSorry}"
