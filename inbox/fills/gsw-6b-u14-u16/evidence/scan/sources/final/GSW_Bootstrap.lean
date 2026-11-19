import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap
open Lean Elab Command

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit
open Encryption.PublicKey

def idsToCheck : List String := ["Bool.toNat_true","Cc.eval_eq","Cc.values_eq","DAGCircuit.toNANDForm_eval","DAGGate.eval_of_isNAND","List.getD_eq_getElem","List.getElem_ofFn","List.length_cons","List.length_ofFn","Nat.cast_one","Nat.clog_one_right","Nat.mul_zero","Nat.pred_succ","Regev.keygen_fst","Regev.keygen_snd","bootGate","bootGate_of_args_eq_cons_cons","bootGate_of_args_eq_nil","bootGate_of_args_eq_singleton","bootNAND_eq","bootNoise_eq","evalKey_eq","fheEvalCircuit_eq","fheEval_eq","h","hG","hargs","hj","hs","if_neg","if_pos","mul_comm","nandFormula_eval","pow_add","pow_mul","pow_succ"]
def scannedModule : Name := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap

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
