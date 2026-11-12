import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ChallengeSim
open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["Bool.false_and","Bool.false_eq_true","Bool.true_and","Bridge.expect_sample_pair","List.length_ofFn","Option.some.injEq","OracleComp.bind_assoc","OracleComp.pure_bind","bne_self_eq_false","chRun_pure","chRun_query_one_none","chRun_query_one_some","chRun_query_zero","expect_bind","expect_const","expect_pure","expect_sub","firstQ_pure","firstQ_query_one","firstQ_query_zero","h","h0","hc","hf","hmap","hneg","hnew","hrep","ht","hx","if_false","ih","show","simulate_pure","simulate_query","sub_self"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim

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
