import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Explicit readings of the nm-sim fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Generic.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["Function.comp_apply","Function.iterate_succ_apply'","List.append_eq_nil_iff","List.drop_left","List.drop_nil","List.drop_succ_cons","List.drop_zero","List.flatMap_cons","List.flatMap_def","List.flatMap_map","List.flatMap_nil","List.flatten_cons","List.flatten_nil","List.length_cons","List.length_drop","List.length_flatten","List.length_nil","List.length_replicate","List.map_cons","List.range_succ_eq_map","List.sum_cons","List.tail_cons","List.tail_drop","List.tail_nil","List.take_left","NUPPT.toCompOn_eq","OracleComp.costBoundedBy_query","OracleComp.pure_bind","OracleComp.query_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_var","ProbComp.expect_bind","ProbComp.expect_const","ProbComp.expect_const_mul","ProbComp.expect_pure","ProbComp.expect_sample","ProbComp.expect_sum","buildComp_succ_of_query","buildComp_succ_of_ret","buildComp_zero_of_ret","chunkEmit_eq","chunkMap_eq","chunkStep_eq","eq_pairEncode_of_pairDecode","expect_congr_of_allOutputs","expect_expect_sample","flatMap_range_drop","funext","h","h.1","hO","hagree","hch","hcons","hit","hl","hnil","hused","hz","if_neg","if_pos","ih","length_pairEncode","pairFstD_of_pairDecode_eq_none","pairFstD_pairEncode","pairSndD_of_pairDecode_eq_none","pairSndD_pairEncode","simulate_eq_of_used","simulate_pure","simulate_query"]

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
