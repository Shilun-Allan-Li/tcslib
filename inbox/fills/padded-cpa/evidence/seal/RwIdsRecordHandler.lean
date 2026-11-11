import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
open Lean Elab Command

/-! Explicit readings of the padded-cpa fill in `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/RecordHandler.lean`: every identifier the added lines pass to
`rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.ChallengeSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["Bool.false_eq_true","GGMRed.ofFn_padFin_of_length","List.drop_succ_cons","List.drop_zero","List.headD_cons","List.headD_nil","List.length_cons","List.length_ofFn","OracleComp.pure_bind","PolyExpr.eval_const","PolyHandler.impl_apply","PolyHandler.input_eq","chRun_pure","chRun_query_one_none","chRun_query_one_some","chRun_query_zero","firstQ_pure","firstQ_query_one","firstQ_query_zero","funext","hans0","hans1","hinit","hs","hw","if_false","if_true","ofFn_zeroBits","pairFstD_pairEncode","pairSndD_pairEncode","recDin_one","recDout_one","recDout_zero","recHandler_run","recHandler_stateLen","recOut_eq","recRun_eq","seedIn_eq","simulate_pure","simulate_query"]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let n := s.toName
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

end TCSlib.Cryptography.Composability.ChallengeSim
