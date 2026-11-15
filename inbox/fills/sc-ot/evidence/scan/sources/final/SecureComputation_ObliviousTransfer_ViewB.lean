import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewB
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.OT
open Complexity Turing TCSlib.Cryptography

def idsToCheck : List String := ["Bool.false_eq_true","Bool.false_xor","Bool.true_xor","Bool.xor_false","Bool.xor_true","Collection.index_eq","Collection.trap_eq","E","Equiv.coe_fn_mk","Equiv.symm_apply_apply","Finset.sum_insert","Fintype.sum_bool","Functionality.idealB_eq","Functionality.realB_eq","HardcoreBit.uexp_add","HardcoreBit.uexp_const_mul","List.drop_left'","List.getD_cons_succ","List.getD_cons_zero","List.headD_cons","List.length_replicate","List.ofFn_const","List.ofFn_succ","List.ofFn_zero","List.take_left'","NUPPT.coinLen_eq","NUPPT.runAt_eq","Option.getD_some","Protocol.viewV_eq","Strategy.encodeMsgs_cons","Strategy.encodeMsgs_nil","Subsingleton.elim","T.f_perm","View.encode_mk","abs_le","accB_eq","acceptProb_comp_equiv","acceptProb_def","acceptProb_idealB","acceptProb_realB","acceptProb_viewDist","add_comm","bobView_eq","distAdv_def","distinguisherL_viewDist","e","hc","hcBit_eq","henc","hev","houtP","hsum","hw","hx","idealB_simBCoins","if_false","if_true","inv_runAtL_ones","isSimB_iff","mask_eq","mask_eval","mask_raw","ofFn_eq_inB1","ofFn_f_fst","ofFn_f_snd","ofFn_inA2","ofFn_inA2_eq","ofFn_inB1","pairFstD_pairEncode","pairSndD_pairEncode","realB_realCoins","realCoins_symm_fst_ofFn","realCoins_symm_snd_ofFn","receiverNext_single","senderNext_single","show","simBCoins_symm_ofFn","simBView_layout","transcriptWith_isOT","uexp_half_add","uexp_half_sub","uprob_bool_prod","uprob_comp_equiv","uprob_not","uprob_predictor_false","uprob_predictor_true","uprob_prod"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewB

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

end TCSlib.Cryptography.SecureComputation.OT
