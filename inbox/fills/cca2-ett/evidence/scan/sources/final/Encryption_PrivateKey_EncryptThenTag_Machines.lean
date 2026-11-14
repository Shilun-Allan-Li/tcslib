import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Machines
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ETTGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["Bool.false_and","Bool.true_and","ChallengeSim.expect_sample_prod","EnsembleLemmas.take_ofFn_coinsEquiv","Function.comp_apply","Function.iterate_one","Function.iterate_succ_apply","Function.iterate_succ_apply'","List.append_nil","List.drop_eq_nil_iff","List.drop_eq_nil_of_le","List.drop_nil","List.drop_succ_cons","List.flatMap_append","List.flatMap_cons","List.flatMap_nil","List.length_append","List.length_cons","List.length_nil","List.length_replicate","List.length_singleton","List.range_succ","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.inArg_eq","NUPPT.inParam_eq","NUPPT.runAtL_eq","NUPPT.runAtL_ofPolyTime","NUPPT.runAt_coinsCongr","NUPPT.runAt_eq","NUPPT.toComp_eq","NUPPT.toOracleAdversary_eq","PolyExpr.eval_subst","PolyExpr.eval_var","bitCodec_decodeMove","bitCodec_timeout","buildComp_of_ret","buildComp_succ_of_query","buildComp_succ_of_ret","buildComp_zero_of_query","buildComp_zero_of_ret","capRaw_eq","cntRead_eq","decide_eq_false","decide_eq_true","decodeBitMove_eq_query_iff.1","decodeBitMove_nil","decodeBitMove_of_not_canonical","decodeBitMove_query","e","eq_zeroBits_of_pairFstD_false","expect_sample_equiv","h","h2","hD","hDc","ha","hcnt","hrun","hsuf","ht","if_neg","if_pos","ih","length_flatMap_range_lt","length_logCount_encodeLog","length_pairEncode","logCount_eq","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","this"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Machines

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

end TCSlib.Cryptography.Composability.ETTGame
