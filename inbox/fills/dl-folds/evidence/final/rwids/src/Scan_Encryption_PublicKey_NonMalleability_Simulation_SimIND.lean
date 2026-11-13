import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimIND
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim
open NMCCA2 (simulate_fwdHandler_impl)
open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
open TCSlib.Cryptography.Games.InteractiveHandler (finA_finInput polyTimeComputable_finA)

def idsToCheck : List String := ["Bool.false_eq_true","Equiv.apply_symm_apply","Equiv.symm_apply_apply","Fintype.card_bool","Fintype.sum_bool","FixedLengthScheme.ofFn_splitHalf_fst","FixedLengthScheme.ofFn_splitHalf_snd","Function.comp_apply","Games.castImpl_eq","Games.padFin_ofFn_zeroBits","InteractiveHandler.advInput_eq","InteractiveHandler.finish_eq","List.append_assoc","List.append_nil","List.drop_append_of_le_length","List.drop_eq_nil_iff","List.drop_left'","List.drop_replicate","List.getElem_map","List.getElem_ofFn","List.getElem_range","List.headD_cons","List.length_drop","List.length_map","List.length_ofFn","List.length_range","List.length_replicate","List.length_take","List.map_map","List.ofFn_const","List.ofFn_inj","List.ofFn_succ","List.replicate_one","List.take_left'","List.take_replicate","NUPPT.advInput_eq","NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn","NUPPT.coins_ofPolyTime","NUPPT.distinguisherL_eq","NUPPT.inAdvice_layout","NUPPT.inArg_eq","NUPPT.inArg_layout","NUPPT.inCoins_eq","NUPPT.inCoins_layout","NUPPT.inParam_eq","NUPPT.inParam_layout","NUPPT.layout_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAtL_ofPolyTime","NUPPT.runAt_coinsCongr","NUPPT.runAt_eq","Option.getD_none","Option.isSome_map","Option.map_map","Option.map_none","Option.map_some","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","ProbComp.expect_sample_equiv","ProbComp.expect_sub","S.inLens_one","S.inLens_zero","S.indImpl_challenge_none_onSpec","S.indImpl_challenge_repeat_onSpec","S.indImpl_dec_onSpec_cast","S.nmCodec_eq_bitCodec","S.nmDecrypt_eq","S.nmGame_eq","S.nmOutput_eq","S.ofFn_nthCt","Subsingleton.elim","accept_eq","badHalves","chunkMap_flatten","coinBlock_eq","copyFin","copyHandler","copyHandler_advInput","copyHandler_finish","decide_eq_false","decide_eq_true","drawWith_eq","encWith_eq","entryL_drop_one","entryL_eq","entryTails_entries","entryTails_eq","eq_const_headD","expect_bind","expect_const","expect_pure","expect_sample","finA_finInput","fun","fwdHandler_advIn","fwdHandler_finCall","fwdHandler_finRun","fwdHandler_outLen","h1","h2","h3","h4","habs","halfDist_blocks","halfDist_distinguisherL","halfFun","halfFunD","halfSamp_runAt","hb","hc","hd","hd0","hd1","hdraw","hdrop","he","headD_ofFn_halfCoins_symm","heq","hes","hfc","hfin","hg1","hgv","hh","hlay","hlen","hnm","hol","hpl","hrun","hsplit","hsub0","hsub0'","hw","hx","hρ","hφ","idealView_eq","if_neg","if_pos","nmOutput_eq_entryTails","ofFn_cast","ofFn_drawWith_half","ofFn_padFin_of_length","ofFn_zeroBits","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","prob_bind","prob_pure","rImpl_dec","rImpl_none_eager","rImpl_none_lazy","rImpl_some","realView_eq","reduceIte","seedIn_eq","simulate_bind","simulate_copyHandler_impl","simulate_pure","snmDin_one","snmDin_zero","tailDist","tailDist_blocks","tailDist_distinguisherL","tailFun"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimIND

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

end TCSlib.Cryptography.Composability.NMSim
