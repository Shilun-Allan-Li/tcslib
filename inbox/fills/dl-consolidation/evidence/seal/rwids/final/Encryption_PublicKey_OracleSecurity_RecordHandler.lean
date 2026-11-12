import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ChallengeSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["Bool.false_eq_true","List.drop_succ_cons","List.drop_zero","List.headD_cons","List.headD_nil","List.length_cons","List.length_ofFn","OracleComp.pure_bind","PolyExpr.eval_const","PolyHandler.impl_apply","PolyHandler.input_eq","chRun_pure","chRun_query_one_none","chRun_query_one_some","chRun_query_zero","firstQ_pure","firstQ_query_one","firstQ_query_zero","hans0","hans1","hinit","hs","hw","if_false","if_true","ofFn_padFin_of_length","ofFn_zeroBits","pairFstD_pairEncode","pairSndD_pairEncode","recDin_one","recDout_one","recDout_zero","recHandler_run","recHandler_stateLen","recOut_eq","recRun_eq","seedIn_eq","show","simulate_pure","simulate_query"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler

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

end TCSlib.Cryptography.Composability.ChallengeSim
