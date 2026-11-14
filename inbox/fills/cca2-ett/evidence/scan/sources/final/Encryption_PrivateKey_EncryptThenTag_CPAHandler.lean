import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.CPAHandler
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ETTGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rAns)
open TCSlib.Cryptography.Composability.PRFGame (pkDin pkDout ctP)

def idsToCheck : List String := ["Bool.false_and","Bool.false_eq_true","Bool.true_and","Collection.ofFn_padFin_of_le","EnsembleLemmas.ofFn_padFin_eq_padL","Fin.val_one","Fin.val_zero","Function.comp_apply","GGMRed.length_tblOf","GGMRed.lookup_tblOf","GGMRed.pairEncode_append_right","GGMRed.tblEnc_cons","GGMRed.tblEnc_nil","GGMRed.tblOf_getElem_fst","GGMRed.tblOf_getElem_snd","InteractiveHandler.advInput_eq","InteractiveHandler.finInput_eq","InteractiveHandler.finish_eq","InteractiveHandler.rAns_eq","InteractiveHandler.rW_input","List.cons_append","List.drop_left'","List.drop_succ_cons","List.drop_zero","List.getD_eq_getElem","List.getElem_map","List.headD_cons","List.headD_nil","List.length_append","List.length_cons","List.length_map","List.length_nil","List.length_ofFn","List.length_replicate","List.map_cons","List.map_nil","List.ofFn_inj","List.replicate_one","List.replicate_succ","List.replicate_zero","List.take_left'","Nat.zero_add","Nat.zero_mul","Option.getD_none","Option.getD_some","Option.isSome_none","Option.isSome_some","PRFGame.pkDin_two","PRFGame.pkDin_zero","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","PrefixByLength.drop_def","bChalKey","bChalTag","bCt","bDKey","bDecAns","bDecL","bDecL_fields","bFin","bFlag","bHandler_finCall","bHandler_outLen","bHandler_perCall","bJ","bKey","bKeyOf_eq","bLook","bNew","bNew_fields","bPad2","bPad2_fields","bRec","bRef","bRun","bSeed","bSeedLen","bStLen","bStLen_eval","bState_eq","bTag","bTape","bTapeOf_eq","bTbl","bWF","ctW_eq","decide_eq_false","decide_eq_true_eq","decide_false","decide_true","encE_eq","ettCt_eval","ettDin_two","ettDin_zero","ettDout_one","ettDout_two","ettDout_zero","h0","hCK","hCT","hDK","hF","hI","hJ","hK","hL","hL'","hR","hRc","hRef","hS","hT","hTag","hTp","hU","hWF","hX","hY","hc","hm","hrec","hx","h₁","h₂","h₃","h₄","if_false","if_neg","if_pos","if_true","ih","keysL_eq","lazyDec_eq","length_pairEncode","length_recBits","length_tblW","log_ne_nil","lookL_eq","lookup_tblW","map_encE_eq_tblOf","ofFn_arrowCongr_finCongr","ofFn_bHSeed","ofFn_bHState","pairFstD_pairEncode","pairSndD_pairEncode","pairV_eq","pairW_eq","recBits_fields","recBits_none","recBits_some","refW_none","refW_some","show","tagLen_eval","tagOf_eq","tblW_cons","tblW_eq","tblW_nil","wC_eq","wR_eq","wT_eq","wfW_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.CPAHandler

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

end TCSlib.Cryptography.Composability.ETTGame
