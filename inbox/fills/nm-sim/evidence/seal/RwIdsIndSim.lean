import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Explicit readings of the nm-sim fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/IndSim.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open AdaptiveCPA (simulate_eq_of_abs)

def idsToCheck : List String := ["Bool.true_and","ChallengeSim.expect_sample_equiv","ChallengeSim.expect_sample_prod","EnsembleLemmas.length_padL","GGMRed.ofFn_padFin_of_length","List.append_assoc","List.drop_left'","List.drop_one","List.drop_replicate","List.drop_succ_cons","List.headD_cons","List.length_append","List.length_ofFn","List.tail_cons","List.take_left'","Nat.add_comm","Option.getD_none","Option.getD_some","Option.map_none","Option.map_some","Option.some.injEq","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","ProbComp.expect_bind","ProbComp.expect_pure","accept_nmGame_eq_rImpl","chalHandler_init","chalHandler_stateLen_eval","decide_eq_decide","drawWith_eq","finMsg_eq","hB","hK","headD_ofFn_chalState","hfin","hs","hybAcc_eq","hφ","hω","length_ofFn_coins","nmAbs_none","nmAbs_snd_fst","nmAbs_some","nmParams_advInput","nmParams_outLen_eval","nmSeed_eq","ofFn_chalState_none","ofFn_chalState_some","ofFn_padFin_eq_padL","ofFn_zeroBits","pairSndD_pairEncode","realView_eq","recDist_distinguisherL","recView_nmOut","recView_nmOutL","samp.runAtL_eq_output_layout","samp.runAt_eq","simulate_bind","simulate_comp","simulate_eq_of_abs","simulate_pure","stParam_eq","stParam_nmAbs"]

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
