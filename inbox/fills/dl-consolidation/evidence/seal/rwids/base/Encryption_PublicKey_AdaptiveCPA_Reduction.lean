import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Reduction
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.AdaptiveCPA
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

def idsToCheck : List String := ["Bool.toNat_false","Bool.toNat_true","GGMRed.ofFn_padFin_of_length","List.getElem?_append_left","List.getElem?_append_right","List.getElem?_eq_none","List.getElem?_nil","List.headD_cons","List.headD_nil","List.length_cons","List.length_nil","List.length_ofFn","List.length_reverse","List.length_singleton","List.reverse_cons","List.reverse_nil","Nat.add_zero","Nat.min_eq_left","Nat.sub_self","Nat.zero_min","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_const","QueryImpl.comp_apply","S.indGame_eq","S.indImpl_challenge_none_onSpec","acAbs","acDout_one","acEnc_eq","acHandler_advInput","acHandler_finish","acHandler_impl_dec","acHandler_impl_eager","acHandler_impl_forward","acHandler_impl_full","acHandler_init_eq","acHandler_outLen","acHyb_eq","accept_eq","castImpl_eq","castImpl_indImpl_challenge","decide_eq_false","decide_eq_true","expect_bind","expect_pure","expect_sample_comm","expect_sample_equiv","expect_sample_prod","expect_tapeImpl","extTape_of_lt","getElem?_reverse_cons","h1","h2","he","headD_ofFn_one","hk","hmin","hsel","hφ","if_neg","if_pos","indCodec_eq_bitCodec","init_acAbs","ofFn_cast","ofFn_select","padFin_ofFn","prob_bind","prob_pure","prob_red_tape","sel_ne","simulate_bind","simulate_comp","simulate_eq_of_abs","simulate_pure","simulate_query","tapeImpl_eager","tapeImpl_full","tapeImpl_lazy","tapeImpl_zero"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Reduction

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

end TCSlib.Cryptography.Composability.AdaptiveCPA
