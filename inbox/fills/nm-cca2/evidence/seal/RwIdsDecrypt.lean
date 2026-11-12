import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
open Lean Elab Command

/-! Explicit readings of the nm-cca2 fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Decrypt.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMCCA2
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open AdaptiveCPA (acDin acDout acDin_zero acDout_zero)

def idsToCheck : List String := ["EnsembleLemmas.padL_eq","Function.comp_apply","InteractiveHandler.advInput_eq","InteractiveHandler.finish_eq","List.flatMap_def","List.flatMap_map","List.length_flatMap","List.length_map","List.length_range","List.length_replicate","List.length_singleton","List.map_append","List.map_cons","List.map_const'","List.map_nil","List.range_succ","List.range_zero","List.sum_replicate","NUPPT.layout_eq","NUPPT.runAt_coinsCongr","NUPPT.runAt_eq","NUPPT.toCompOn_eq","Nat.add_zero","OracleComp.pure_bind","PolyExpr.eval_const","PrefixByLength.drop_def","acDin_zero","ansRead_eq","bitCodec_encodeEntry","buildComp_succ_of_query","buildComp_zero_of_ret","cntRead_eq","dCnt","dCt","dFin","dIn","decBlock_eq","decHandler","decHandler_finCall","decHandler_outLen","decide_eq_false","fwdHandler_advIn","fwdHandler_finCall","fwdHandler_finRun","fwdHandler_outLen","fwdHandler_perCall","fwdHandler_seedLen","h0","hA","hB'","hB₁","hCt","hIn","hL","hO","hU","hW","hZ","hc","hctl","hfin","hh","hhist","hout","hw","id_eq","if_neg","if_pos","length_logEmit_cntRead","logEmit_ansRead","logEmit_encodeLog","mul_one","ofFn_padFin_eq_take","pairFstD_nil","pairFstD_pairEncode","pairSndD_of_pairDecode_eq_none","pairSndD_pairEncode","seedIn_eq","simulate_pure","simulate_query","smul_eq_mul"]

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
