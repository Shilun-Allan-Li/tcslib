import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim Compose
open TCSlib.Cryptography.SecureComputation.ComposeSim
open TCSlib.Cryptography.SecureComputation.HybridProtocol

def idsToCheck : List String := ["Equiv.trans_apply","Fin.coe_divNat","Fin.coe_modNat","FunFamily.blocks_symm_apply","Functionality.realA_eq","Functionality.realB_eq","H.answersRealA_eq_answersA","H.answersRealB_eq_answersB","H.runInputA_of_ge","H.runInputA_of_lt","H.runInputB_of_ge","H.runInputB_of_lt","List.append_nil","List.drop_drop","List.drop_left'","List.flatMap_append","List.flatMap_map","List.flatMap_nil","List.flatMap_singleton","List.getElem_ofFn","List.length_ofFn","List.length_replicate","List.ofFn_fin_append","List.ofFn_mul","List.range_add","List.range_succ","List.range_zero","List.replicate_zero","List.take_left'","Nat.add_comm","Nat.add_mul_div_right","Nat.add_mul_mod_self_right","Nat.div_eq_of_lt","Nat.mod_eq_of_lt","Nat.mul_comm","Nat.succ_mul","Nat.zero_add","Nat.zero_mul","Protocol.outP_eq","Protocol.outV_eq","Protocol.transcriptWith_eq","Protocol.transcript_eq_transcriptWith","Protocol.viewP_eq","Protocol.viewV_eq","Strategy.coinLen_eq","Strategy.encodeMsgs_nil","View.encode_mk","answersA_eq","answersB_eq","answersRealA_eq","answersRealB_eq","asmView_eq","beq_true","coinBlock_eq","composeCoins_fst","composeCoins_snd","compose_P_coinLen","compose_V_coinLen","compose_outP","compose_outV","compose_viewP","compose_viewV","dif_neg","dif_pos","encodeMsgs_append","encodeMsgs_eq_flatMap","exec_eq_map","flatMap_range_congr","flatMap_range_mul","flatten_ofFn_eq_flatMap_range","hL","hN","hT0","hblk","hg","hmain","hmsgs","htape","inA_eq","inB_eq","mainExec_eq","ofFn_arrowCongr_finCongr","ofFn_blocks_symm","ofFn_composeCoins_fst","ofFn_composeCoins_snd","ofFn_padFin","ofFn_splitCoins","padTo_of_length","pairFstD_pairEncode","pairSndD_pairEncode","privA_eq","privB_eq","realViewA_eq","realViewB_eq","runExec_composeCoins","runExec_eq","runInputA_composeCoins","runInputB_composeCoins","runMsg_composeCoins","runMsg_eq","runTape_eq","runTape_ofFn_splitCoins","segW_encodeMsgs","show","slotFromA_mul_add","slotFromB_mul_add","splitCoins_eq","take_ofFn_splitCoins"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> (Pure.pure [] : CoreM (List Name))
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
