import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
open Lean Elab Command

namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open AdaptiveCPA NMCCA2 ProbComp ChallengeSim
open TCSlib.Cryptography.Composability.FixedLengthPKScheme

def idsToCheck : List String := ["Bool.not_false","Bool.not_true","Bool.true_and","EnsembleLemmas.length_padL","EnsembleLemmas.padL_eq","Equiv.trans_apply","FixedLengthPKScheme.indCodec_eq_bitCodec","FixedLengthScheme.decOpen_cca2","FunFamily.ofFn_blocks","Games.castImpl_eq","INDSecure_iff","List.drop_left'","List.drop_zero","List.getElem_map","List.getElem_ofFn","List.getElem_range","List.headD_cons","List.length_append","List.length_drop","List.length_map","List.length_ofFn","List.length_range","List.length_singleton","List.take_append_of_le_length","List.take_left'","List.take_of_length_le","NMSecure_iff","NUPPT.coinsEquivPoly_ofFn","NUPPT.distinguisherL_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAt_eq","Nat.one_mul","Nat.succ_mul","Nat.zero_mul","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","ProbComp.expect_sample_comm","ProbComp.expect_sample_equiv","S.enc_length","S.indGame_eq","S.indImpl_dec_onSpec_cast","S.indImpl_eq_of_msgLen_eq_zero","S.nmDecrypt_eq","S.nmGame_eq","S.outLens_zero","acDin_zero","acDout_zero","accept_eq","advantage_eq","advantage_self","decAnswers_eq_nmOutput","decBlock_eq","decBlock_eq_nthCt","decHandler_advInput","decHandler_outLen","decide_eq_false","decide_eq_true","encCt_eq","encHandler_advInput","encHandler_finish","encHandler_outLen","expect_bind","expect_pure","expect_sample_prod","guessDist_distinguisherL","guessDist_nmOutput","h1","h2","hB'","hW","ha","hblk","hc","hct","hd1","hdecB","headD_ofFn_one","hg","hi","hin","hlen","hout","hw","hφ","if_neg","if_pos","key","nmCodec_eq_bitCodec","nmDecrypt","nmOutput_eq","ofFn_cast","ofFn_nthCt","ofFn_padFin_eq_take","ofFn_padFin_of_length","ofFn_zeroBits","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","prob_bind","prob_pure","simulate_bind","simulate_decHandler_finish","simulate_decHandler_impl","simulate_encHandler_impl","simulate_pure"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability

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

end TCSlib.Cryptography.Composability
