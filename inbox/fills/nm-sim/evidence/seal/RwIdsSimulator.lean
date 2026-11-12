import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Explicit readings of the nm-sim fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Simulator.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open NMCCA2 (finU finA fields_finInput polyTimeComputable_finFields)
open AdaptiveCPA (simulate_eq_of_abs)

def idsToCheck : List String := ["Bool.and_true","Bool.true_and","ChallengeSim.expect_sample_comm","ChallengeSim.expect_sample_equiv","ChallengeSim.expect_sample_prod","EnsembleLemmas.padL_eq","Fin.val_zero","Function.comp_apply","GGMRed.ofFn_padFin_of_length","InteractiveHandler.advInput_eq","InteractiveHandler.finInput_eq","List.append_assoc","List.drop_left'","List.drop_one","List.flatten_append","List.flatten_singleton","List.headD_cons","List.length_append","List.length_cons","List.length_drop","List.length_ofFn","List.length_replicate","List.map_append","List.map_map","List.map_singleton","List.mem_range","List.range_succ","List.replicate_eq_nil_iff","List.replicate_succ'","List.replicate_zero","List.tail_cons","List.take_left'","List.take_zero","NUPPT.Uniform.runAt_eq","NUPPT.advInput_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAt_eq","Nat.mul_add","Nat.mul_one","Option.getD_none","Option.map_some","Option.some.injEq","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","ProbComp.expect_bind","ProbComp.expect_pure","QueryImpl.comp_apply","chalHandler_advIn","chalHandler_finCall","chalHandler_finRun","chalHandler_impl_dec","chalHandler_impl_none","chalHandler_impl_some","chalHandler_init","chalHandler_outLen","chalHandler_seedLen","chunkAt_eq","chunkAt_flatten_append","chunkMap_flatten","decide_eq_decide","decide_eq_true","decide_eq_true_eq","drawWith_eq","drop_flatten_append","encWith_eq","expect_simulate_rImpl_eager","finSt","finSt_finInput","flagF_eq","hA","hH","hQ","hSim","hU","hW","hZ","ha","hc","hct","hd","headD_ofFn_chalState","hent","hfin","histImpl_eq","hq","hrep","hst","hybAcc_eq","hφ","idealAcc_eq","idealView_eq","idealView_simOut","if_neg","if_pos","ih","length_chunkAt","length_flagF","length_flatten_map_range","ofFn_chalState_some","ofFn_padFin_eq_padL","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","rImpl_dec_cpa","rImpl_none_eager","rImpl_some","rdAns_input","realView_eq","seedEquiv_ofFn","seedIn_eq","simAbs_none","simAbs_snd","simAbs_some","simCt_eq","simCt_input","simFin_eq","simMsg_eq","simOutL_eq","simParams_advIn","simParams_advInput","simParams_ansH","simParams_ansY","simParams_finCall","simParams_finRun","simParams_j","simParams_outLen","simParams_outLen_eval","simParams_qry","simParams_seedLen","simulate_bind","simulate_comp","simulate_eq_of_abs","simulate_pure","simulate_query","snmDin_one","take_eq_flatten_chunkAt","toCompOn_budget_eq"]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let s' := if s.startsWith "S." then "FixedLengthPKScheme." ++ (s.drop 2) else
      if s.startsWith "M." then "MsgSampler." ++ (s.drop 2) else
      if s.startsWith "samp." then "Complexity.NUPPT." ++ (s.drop 5) else s
    let n := s'.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> pure []
    let env ← getEnv
    let modOf (c : Name) : String :=
      ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!.toString).getD "?"
    if cands.isEmpty then IO.println s!"{s}: (unresolved: local hypothesis or private)"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some _ => "other"
        | none => "?"
      IO.println s!"{s}: {c}: {k} ({modOf c})"

end TCSlib.Cryptography.Composability.NMSim
