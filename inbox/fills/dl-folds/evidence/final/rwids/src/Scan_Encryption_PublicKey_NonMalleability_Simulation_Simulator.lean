import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Simulator
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
open TCSlib.Cryptography.EnsembleLemmas (seedEquiv seedEquiv_ofFn ofFn_padFin_eq_padL)
open TCSlib.Cryptography.Games.InteractiveHandler (rU_input rZ_input rW_input rX_input rAns_input rU_finInput rS_finInput finA_finInput polyTimeComputable_rU polyTimeComputable_rZ polyTimeComputable_rW polyTimeComputable_rS polyTimeComputable_rX polyTimeComputable_rAns polyTimeComputable_finA)

def idsToCheck : List String := ["Bool.and_true","Bool.true_and","ChallengeSim.expect_sample_prod","EnsembleLemmas.padL_eq","Fin.val_zero","Function.comp_apply","Games.simulate_eq_of_abs","InteractiveHandler.advInput_eq","List.append_assoc","List.drop_left'","List.drop_one","List.flatten_append","List.flatten_singleton","List.headD_cons","List.length_append","List.length_cons","List.length_drop","List.length_ofFn","List.length_replicate","List.map_append","List.map_map","List.map_singleton","List.mem_range","List.range_succ","List.replicate_eq_nil_iff","List.replicate_succ'","List.replicate_zero","List.tail_cons","List.take_left'","List.take_zero","NUPPT.Uniform.runAt_eq","NUPPT.advInput_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAt_eq","NUPPT.toCompOn_budget_eq","Nat.mul_add","Nat.mul_one","Option.getD_none","Option.map_some","Option.some.injEq","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","ProbComp.expect_bind","ProbComp.expect_pure","ProbComp.expect_sample_comm","ProbComp.expect_sample_equiv","QueryImpl.comp_apply","chalHandler_advIn","chalHandler_finCall","chalHandler_finRun","chalHandler_impl_dec","chalHandler_impl_none","chalHandler_impl_some","chalHandler_init","chalHandler_outLen","chalHandler_seedLen","chunkMap_flatten","coinBlock_eq","coinBlock_flatten_append","decide_eq_decide","decide_eq_true","decide_eq_true_eq","drawWith_eq","drop_flatten_append","encWith_eq","expect_simulate_rImpl_eager","flagF_eq","hA","hH","hQ","hSim","hU","hW","hZ","ha","hc","hct","hd","headD_ofFn_chalState","hent","hfin","histImpl_eq","hq","hrep","hst","hybAcc_eq","hφ","idealAcc_eq","idealView_eq","idealView_simOut","if_neg","if_pos","ih","length_coinBlock","length_flagF","length_flatten_map_range","ofFn_chalState_some","ofFn_padFin_eq_padL","ofFn_padFin_of_length","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","rAns_input","rImpl_dec_cpa","rImpl_none_eager","rImpl_some","rS_finInput","rU_input","rX_input","realView_eq","seedEquiv_ofFn","seedIn_eq","simAbs_none","simAbs_snd","simAbs_some","simCt_eq","simCt_input","simFin_eq","simMsg_eq","simOutL_eq","simParams_advIn","simParams_advInput","simParams_ansH","simParams_ansY","simParams_finCall","simParams_finRun","simParams_j","simParams_outLen","simParams_outLen_eval","simParams_qry","simParams_seedLen","simulate_bind","simulate_comp","simulate_pure","simulate_query","snmDin_one","take_eq_flatten_chunkAt"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Simulator

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
