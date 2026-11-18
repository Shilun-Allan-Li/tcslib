import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula
open Lean Elab Command

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit
open Encryption.PublicKey

def idsToCheck : List String := ["FormulaArith.modSumInterval_eval","LWE.BitEncoding.decodeHi_eq","LWE.BitEncoding.decodeLo_eq","LWE.BitEncoding.decode_iff_mem_Ico","Matrix.dotProduct_mulVec","Nat.cast_mul","Nat.cast_sum","TreeCircuit.and2_eval","TreeCircuit.depth_neg","TreeCircuit.maxFanin_neg","TreeCircuit.neg_eval","ZMod.natCast_zmod_val","ZMod.val_natCast","decConstants_eq","decDepth_eq","decide_eq_true_iff","decryptFormula_eq","decryptFormula_eval","decrypt_eq_decode_dotProduct","dotProduct_comm","gadget_mulVec_decomposeVec","hcast","ht","hval","keyBits_eq","nandFormula_eq","vecMul_secretVector_eq_sum"]
def scannedModule : Name := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> pure []
    if cands.isEmpty then IO.println s!"{s}\t-\tlocal/unresolved\t-"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some (.opaqueInfo _) => "opaque"
        | some (.inductInfo _) => "inductive"
        | some (.ctorInfo _) => "ctor"
        | some _ => "other"
        | none => "?"
      let m := modOf c
      let tag := if k == "DEF" then
          (if m == scannedModule then "own-def" else if (`TCSlib).isPrefixOf m then "FOREIGN-TCSLIB-DEF" else "core/mathlib-def")
        else k
      IO.println s!"{s}\t{c}\t{tag}\t{m}"

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
