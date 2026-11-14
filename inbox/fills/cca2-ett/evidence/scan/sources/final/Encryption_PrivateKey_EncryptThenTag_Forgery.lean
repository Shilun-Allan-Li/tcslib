import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Forgery
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ETTGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","Bool.and_eq_true","Bool.false_eq_true","Bool.false_or","Bool.not_eq_true","Bool.true_or","Fintype.card_bool","Fintype.card_fin","Fintype.card_fun","Function.update_of_ne","Function.update_self","List.length_ofFn","List.length_singleton","List.map_cons","List.mem_cons","List.mem_singleton","Nat.cast_sub","OracleComp.bind_assoc","OracleComp.pure_bind","abs_le","ctW_eq","decAnsW_agree","decAnsW_eq","decide_eq_true_eq","e","encW_eq_ctW","eq_ctW_of_wfW","ettAcc_eq","ettBad_apply","ettImpl_apply","ettStep_challenge_none","ettStep_challenge_some","ettStep_dec","ettStep_enc","expect_add","expect_bind","expect_const","expect_const_mul","expect_pure","expect_sample_comm","expect_sample_coord","expect_sample_ovr","expect_sub","h","h.1.2.2","h0","hans","hc","hcc","hd","hfst","hi2","hitQ_one","hitQ_two","hitQ_zero","hitW_eq","hl","hp","hpc","hr","hs","ht","hv","hw","hweq","hy","if_false","if_neg","if_pos","length_pairEncode","one_div","ovr_cons","ovr_nil","ovr_of_mem","ovr_of_not_mem","padFin_ofFn","pairW_eq","prob_bad_of_flag","prob_bind","prob_eq_expect","prob_pure","prob_simulate_ettBad_query","refW_some","show","simulate_ettBad_fst","simulate_pure","simulate_query","tagL_eq","this","true_or","validW_eq","validW_pairW","wC_ctW","wR_ctW","wfW_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Forgery

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
