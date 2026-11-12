import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.QueryHandler
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.BitwiseSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim

def idsToCheck : List String := ["Bool.false_eq_true","GGMRed.ofFn_padFin_of_length","List.drop_succ_cons","List.drop_zero","List.headD_cons","List.headD_nil","List.length_cons","List.length_ofFn","List.length_replicate","Option.getD_some","OracleComp.pure.injEq","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyHandler.advInput_eq","PolyHandler.answer_of_pairDecode_eq_some","PolyHandler.impl_apply","PolyHandler.input_eq","PolyHandler.result_eq","Prod.mk.injEq","chRun_pure","chRun_query_one_none","chRun_query_one_some","chRun_query_zero","decodeFin_eq","decodeFin_nil_getD","decodeFin_ofFn","firstQ_pure","firstQ_query_one","firstQ_query_zero","hadv","hans1","haux","hinit","hs","hs'","hsim","ht","hw","hxlen","h₁","h₂","if_false","if_true","length_pairEncode","pairFstD_pairEncode","pairSndD_pairEncode","qDin_one","qDout_one","qHandler_advIn","qHandler_answer_dec","qHandler_out","qHandler_run","qHandler_stateLen","qRun_eq","recAdvIn_eq","seedIn_eq","show","simulate_pure","simulate_query"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.QueryHandler

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

end TCSlib.Cryptography.Composability.BitwiseSim
