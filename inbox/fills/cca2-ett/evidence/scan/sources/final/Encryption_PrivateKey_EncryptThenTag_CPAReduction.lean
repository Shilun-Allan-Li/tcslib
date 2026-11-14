import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.CPAReduction
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ETTGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
open TCSlib.Cryptography.Composability.PRFGame (pkDin pkDout ctP fImpl atkOf qRed ctOf)

def idsToCheck : List String := ["AdaptiveCPA.extTape_of_lt","AdaptiveCPA.msgOf_eq","ChallengeSim.expect_sample_prod","List.length_cons","List.length_ofFn","NUPPT.runAt_coinsCongr","NUPPT.runAt_eq","NUPPT.toCompOn_eq","NUPPT.toComp_eq","Option.map_none","Option.map_some","OracleComp.bind_assoc","OracleComp.pure_bind","PRFGame.ctOf_eq","PRFGame.ctP_eval","PRFGame.fImpl_challenge_none","PRFGame.fImpl_enc","PRFGame.length_ctOf","PRFGame.pkDin_two","PRFGame.pkDin_zero","PRFGame.pkDout_two","PRFGame.pkDout_zero","PRFGame.qRed_eval","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_var","QueryImpl.comp_apply","bAbs_eq","bHandler_advInput","bHandler_finCall","bHandler_finish","bHandler_impl_challenge_none","bHandler_impl_challenge_some","bHandler_impl_dec","bHandler_impl_enc","bHandler_init_hstate","bHandler_outLen","bHandler_perCall","bInv_iff","bKeyOf_ctOf","bKeyOf_eq","bTapeOf_eq","bTapes_eq","bTapes_of_lt","cpaRec_eq","ctW_eq","ettAcc_eq","ettCt_eval","ettDin_two","ettDin_zero","ettLazyK_eq","ettLazyTape_eq","expect_bind","expect_const","expect_ettImpl_lazy","expect_ettLazyTape","expect_pure","expect_sample_comm","expect_sample_equiv","expect_simulate_abs_inv","expect_toCompOn_outLen","hB'","hB'B","hQ","hk","hrec","hrun","htbl","hx","hx'","hxx","hφ₀","hφ₂","id_eq","keysL_nil","lazyStep_challenge_none","lazyStep_challenge_some","lazyStep_dec","lazyStep_enc","length_maskL","length_pairEncode","maskL_eq","ofFn_ctOf","ofFn_padFin_of_length","ovr_nil","pairFstD_pairEncode","pairSndD_pairEncode","pairV_eq","show","simulate_bind","simulate_comp","simulate_pure","simulate_query","tagTbl_none_nil","tapeImpl_apply","wC_ctW","wR_ctW"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.CPAReduction

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
