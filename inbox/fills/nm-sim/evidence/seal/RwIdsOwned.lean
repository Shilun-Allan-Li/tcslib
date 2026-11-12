import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Explicit readings of the nm-sim fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.FixedLengthPKScheme
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open NMSim
open AdaptiveCPA (castImpl castImpl_eq expect_simulate_castImpl_toCompOn padFin_ofFn_zeroBits)

def idsToCheck : List String := ["Fin.cons_succ","Fin.cons_zero","List.headD_cons","List.length_ofFn","List.ofFn_fin_append","List.ofFn_succ","List.tail_cons","M.draw_eq","M.histAt_eq","NMSim.hybAcc_true_eq_false","NMSim.realAcc_eq_hybAcc","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","ProbComp.prob_bind","ProbComp.prob_pure","S.NMSecure_iff","S.snmImpl_challenge","S.snmImpl_dec","abs_mul","abs_neg","abs_two","abs_zero","accept_eq","accept_snmIdeal_eq","accept_snmReal_eq","advantage_eq","castImpl_eq","castImpl_snmImpl","decide_map_ofFn","drawWith_eq","encWith_eq","entryL_eq","hB","hSim","hab","hc","histImpl_eq","histWith_eq","hx","idealAcc_eq","idealView_eq","if_neg","if_pos","ofFn_block","ofFn_natAdd_eq_drop","ofFn_snmEntry","ofFn_zeroBits","padFin_ofFn_zeroBits","rImpl_dec","rImpl_none_eager","rImpl_none_lazy","rImpl_some","realAcc_eq","realView_eq","simEntry_fst","simImpl_eq","simImpl_eq_histImpl","snmCt_eq","snmDin_one","snmDin_zero","snmDout_one","snmDout_zero","snmEntry_eq","snmIdeal_eq","snmInLens_one","snmInLens_zero","snmOutLens_one","snmOutLens_zero","snmReal_eq","snmSigma_eq","snmView_eq","snmView_idealView","snmView_realView","sub_self"]

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

end TCSlib.Cryptography.Composability.FixedLengthPKScheme
