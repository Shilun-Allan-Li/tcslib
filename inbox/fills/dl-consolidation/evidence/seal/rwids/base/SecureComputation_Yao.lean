import TCSlib.Cryptography.SecureComputation.Yao
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography BoolCircuit
open TCSlib.Cryptography.SecureComputation.YaoCircuit

def idsToCheck : List String := ["Bool.xor_assoc","Bool.xor_false","Bool.xor_self","Equiv.symm_apply_apply","Fin.val_mk","HybridProtocol.answersB_eq","HybridProtocol.pairFstD_privA","HybridProtocol.pairSndD_privB","List.flatten_cons","List.getD_eq_default","List.getD_eq_getElem","List.getElem_ofFn","List.ofFn_succ","PolyExpr.eval_const","Protocol.outP_eq","Protocol.outV_eq","Protocol.transcriptWith_eq","Strategy.encodeMsgs_cons","YaoCircuit.output_apply","decide_eq_true","decodeMsgs_encodeMsgs","decodeMsgs_nil","decodeOut","dif_neg","dif_pos","encodeCircuit_eq","encodeMsgs_inj","exec_succ","exec_zero","finProdFinEquiv_apply_val","garbledValues_eq","garbledValues_getD","getD_ofFn'","h","hans","hb","hj","hv'","hx","hy","h₁","if_neg","if_pos","ih","inputKeys_eq","keyAt_eq","moverIsV_false","otFunctionality_f_snd_apply","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","readBits_apply","show","tableAt_eq","yaoAlice_next_cons","yaoAlice_next_nil","yaoBobInit_eq","yaoBobInit_yaoMsg","yaoBobOut_eq","yaoBobTables_eq","yaoBobTables_yaoMsg","yaoBobValues_eq","yaoBobValues_yaoMsg","yaoBob_next","yaoCall","yaoCall_finProdFinEquiv","yaoHybrid_answersB_getD","yaoHybrid_callA","yaoHybrid_callB","yaoKeysA_eq","yaoMain_P","yaoMain_V","yaoMain_outP","yaoMain_outV","yaoMain_rounds","yaoMain_verifierFirst","yaoMsg_eq","yaoPairs_eq","yaoSeed_fst","yaoTables_eq"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.Yao

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

end TCSlib.Cryptography.SecureComputation
