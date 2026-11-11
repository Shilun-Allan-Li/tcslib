import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA
open Lean Elab Command

/-! Explicit readings of the bitwise-cpa fill in `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/QueryHandler.lean`: every identifier the added lines pass to
`rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.BitwiseSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim

def idsToCheck : List String := ["Bool.false_eq_true","GGMRed.ofFn_padFin_of_length","List.drop_succ_cons","List.drop_zero","List.headD_cons","List.headD_nil","List.length_cons","List.length_ofFn","List.length_replicate","Option.getD_some","OracleComp.pure.injEq","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyHandler.advInput_eq","PolyHandler.answer_of_pairDecode_eq_some","PolyHandler.impl_apply","PolyHandler.input_eq","PolyHandler.result_eq","Prod.mk.injEq","chRun_pure","chRun_query_one_none","chRun_query_one_some","chRun_query_zero","decodeFin_eq","decodeFin_nil_getD","decodeFin_ofFn","firstQ_pure","firstQ_query_one","firstQ_query_zero","funext","hadv","hans1","haux","hinit","hs","hs'","hsim","ht","hw","hxlen","h₁","h₂","if_false","if_true","length_pairEncode","pairFstD_pairEncode","pairSndD_pairEncode","qDin_one","qDout_one","qHandler_advIn","qHandler_answer_dec","qHandler_out","qHandler_run","qHandler_stateLen","qRun_eq","recAdvIn_eq","seedIn_eq","simulate_pure","simulate_query"]

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

end TCSlib.Cryptography.Composability.BitwiseSim
