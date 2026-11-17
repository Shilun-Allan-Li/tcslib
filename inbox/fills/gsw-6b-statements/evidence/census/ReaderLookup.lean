import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
import TCSlib.Cryptography.LWE

/-! Reader lookup (gsw-6b statements, sub-agent probe; check 6 census). For each foreign definition
in `deflist.txt` (census6b.py), print its module and line and every TCSlib theorem whose last name
component starts with the definition's last component and `_` (case-insensitive) and whose
statement mentions the definition, with module and line, plus whether the reader is proved by
`rfl`/`Iff.rfl` (its value is `rfl`/`Eq.refl`/`Iff.rfl`, or depends on no `sorryAx`). -/

open Lean Elab Command

def defs : List Name := [`BoolCircuit.DAGCircuit.IsLayered, `BoolCircuit.DAGCircuit.IsNANDForm, `BoolCircuit.DAGCircuit.depth, `BoolCircuit.DAGCircuit.depthAt, `BoolCircuit.DAGCircuit.eval, `BoolCircuit.DAGCircuit.layerNAND, `BoolCircuit.DAGCircuit.toNANDForm, `BoolCircuit.DAGCircuit.values, `BoolCircuit.DAGGate.IsNAND, `BoolCircuit.DAGGate.depth, `BoolCircuit.DAGGate.eval, `BoolCircuit.FormulaArith.modSumDepth, `BoolCircuit.FormulaArith.modSumInterval, `BoolCircuit.TreeCircuit.and2, `BoolCircuit.TreeCircuit.depth, `BoolCircuit.TreeCircuit.eval, `BoolCircuit.TreeCircuit.maxFanin, `BoolCircuit.TreeCircuit.neg, `BoolCircuit.litInput, `BoolCircuit.runWith, `BranchingProgram.Instr.stepWith, `BranchingProgram.IsFiveCycle, `BranchingProgram.IsPermutation, `BranchingProgram.barrington, `BranchingProgram.evalWith, `BranchingProgram.length, `BranchingProgram.sigma1, `BranchingProgram.yield, `Complexity.NUPPT.coinLen, `Complexity.NUPPT.distinguisherL, `Complexity.P, `Complexity.PolyExpr.eval, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Encrypts, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.columns, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.ofFamily, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.bootGate, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.bootNoise, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.challengeDist, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.challengeTerm, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decDepth, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decomposeVec, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decrypt, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decryptColumn, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.encrypt, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.eval, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.evalKey, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.fheEvalCircuit, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.fheView, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.gadget, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.homAnd, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.homEvalFormula, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.homNot, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.keyBits, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.levelKey, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.levelReduction, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.levelTerm, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.leveledEvalCircuit, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.leveledView, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.mul, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.nandFormula, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.realView, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.reduction, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.secretVector, `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.view, `TCSlib.Cryptography.Encoding.Modular.encodeMatrix, `TCSlib.Cryptography.Encryption.PublicKey.Regev.extractionError, `TCSlib.Cryptography.Encryption.PublicKey.Regev.keygen, `TCSlib.Cryptography.LWE.BitEncoding.decode, `TCSlib.Cryptography.LWE.BitEncoding.decodeHi, `TCSlib.Cryptography.LWE.BitEncoding.decodeLo, `TCSlib.Cryptography.LWE.DLWEAssumption, `TCSlib.Cryptography.LWE.Family.advantageAt, `TCSlib.Cryptography.LWE.Noise.Bounded, `TCSlib.Cryptography.LWE.decisionAdvantage, `TCSlib.Cryptography.LWE.encodeChallenge, `TCSlib.Cryptography.LWE.sample, `TCSlib.Cryptography.Negligible, `TCSlib.Cryptography.acceptProb, `TCSlib.Cryptography.distAdv, `TCSlib.Cryptography.hybridPlant, `TCSlib.Cryptography.uprob]

def lineOf (n : Name) : CommandElabM String := do
  match ← findDeclarationRanges? n with
  | some r => return toString r.selectionRange.pos.line
  | none => return "?"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf := fun (n : Name) => match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]! | none => `_
  let thms := env.constants.map₁.toList.filter fun (n, ci) =>
    ci matches .thmInfo _ && (`TCSlib).isPrefixOf (modOf n) && !n.isInternalDetail
  for d in defs do
    let some _ := env.find? d | IO.println s!"NOTFOUND\t{d}"
    let last := (d.componentsRev.headD .anonymous).toString.toLower
    let mut rs : Array String := #[]
    for (t, ci) in thms do
      let tl := (t.componentsRev.headD .anonymous).toString.toLower
      if tl.startsWith (last ++ "_") && ci.type.getUsedConstants.contains d then
        let sorryFree := !(ci.value!.getUsedConstants.contains ``sorryAx)
        rs := rs.push s!"{t}@{modOf t}:{← lineOf t}{if sorryFree then "" else "[admitted]"}"
    IO.println s!"READERS\t{d}\t{modOf d}:{← lineOf d}\t{if rs.isEmpty then "MISSING" else " ".intercalate rs.toList}"
