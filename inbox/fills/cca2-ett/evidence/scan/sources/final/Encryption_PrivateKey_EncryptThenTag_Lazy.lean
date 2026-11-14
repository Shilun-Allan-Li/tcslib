import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Lazy
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ETTGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","Bool.and_eq_true","Bool.and_true","Bool.false_or","Bool.not_eq_true","Bool.not_false","Bool.not_true","Bool.true_and","Function.update_eq_self","Function.update_of_ne","List.append_nil","List.cons.injEq","List.cons_append","List.getD_cons_succ","List.getD_eq_getElem","List.idxOf_cons","List.length_map","List.length_ofFn","List.map_append","List.map_cons","List.map_map","List.map_nil","List.mem_append","List.mem_cons","List.mem_singleton","List.nil_append","List.zipWith_cons_cons","Option.getD_none","Option.getD_some","OracleComp.bind_assoc","OracleComp.pure_bind","Prod.mk.eta","cond_false","ctW_eq","decAnsW_eq","decAnsW_tagTbl","decL_eq","decide_eq_true","decide_eq_true_eq","e","encW_eq_ctW","ettImpl_apply","ettLazy_apply","ettLazy_eq","ettStep_challenge_none","ettStep_challenge_some","ettStep_dec","ettStep_enc","expect_bind","expect_const","expect_pure","expect_sample_comm","expect_sample_ovr","false_or","freshImpl_apply","h","hd","hi0","hi2","hk","hl","hp","hr","hrec","htbl","hw","hy","h₁","h₂","if_neg","if_pos","ih","keysL_cons","keysL_eq","keys_tagTbl","lazyDec_eq","lazyStep_challenge_none","lazyStep_challenge_some","lazyStep_dec","lazyStep_enc","length_pairEncode","lookL_eq","maskL_eq","ovr_append","ovr_append_of_mem","ovr_append_of_not_mem","ovr_cons","ovr_cons_self","ovr_nil","ovr_of_not_mem","ovr_tags_of_mem","ovr_update","padFin_ofFn","pairW_eq","reduceIte","show","simulate_pure","simulate_query","tagL_eq","tagOf_eq","tagOf_eq_ovr","tagTbl_cons","tagTbl_eq","this","validW_eq","wC_ctW","wR_ctW","wT_ctW","wfW_eq","zipWith_xor_cancel"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Lazy

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
