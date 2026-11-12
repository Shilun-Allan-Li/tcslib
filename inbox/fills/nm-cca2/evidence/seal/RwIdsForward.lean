import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
open Lean Elab Command

/-! Explicit readings of the nm-cca2 fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Forward.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMCCA2
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games


def idsToCheck : List String := ["Function.iterate_succ_apply","Function.iterate_succ_apply'","InteractiveHandler.call_eq","InteractiveHandler.finInput_eq","InteractiveHandler.impl_apply","InteractiveHandler.input_eq","List.drop_nil","List.drop_succ_cons","List.drop_zero","List.flatMap_cons","List.flatMap_map","List.flatMap_nil","List.length_cons","List.nil_append","List.ofFn_fin_append","List.range_succ_eq_map","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","OracleComp.pure_bind","OracleComp.query_bind","PolyExpr.eval_const","PolyExpr.eval_var","and_self","bitCodec_encodeEntry","buildComp_succ_of_query","buildComp_zero_of_ret","finA","finL","finU","finW","finZ","fwdHandler_impl","fwdHandler_perCall","fwdRun","hA","hI","hL","hS","hX","hcons","hlog","hnil","if_neg","if_pos","ih","iterate_pairSndD_encodeLog","length_pairEncode","logEmit_eq","pairFstD_pairEncode","pairSndD_of_pairDecode_eq_none","pairSndD_pairEncode","rAns","rIdx","rLog","rQuery","rState","seedIn_eq","simulate_pure","simulate_query"]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let s' := if s.startsWith "S." then "FixedLengthPKScheme." ++ (s.drop 2) else s
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

end TCSlib.Cryptography.Composability.NMCCA2
