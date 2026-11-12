import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Collision
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.PRFGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","Bool.false_and","Bool.false_eq_true","Bool.false_or","Bool.not_eq_true","Bool.or_false","Bool.true_or","List.getElem_zipWith","List.length_map","List.length_nil","List.length_ofFn","List.length_singleton","List.lookup_cons","List.lookup_nil","List.map_cons","Nat.cast_one","Nat.cast_zero","Option.getD_none","Option.isSome_none","Option.map_none","abs_le","addPt_eq","addPt_eq_of","ctOf_eq","ctOf_xorPerm","decide_eq_false_iff_not","div_eq_mul_one_div","expect_add","expect_bind","expect_const","expect_pure","expect_sample_comm","flag_addPt","h","hK","hY","hatk","hb","hcard","hi2","hitStar_none","hitStar_some","hml","hs","hv","hx","h₀","h₁","if_false","if_neg","if_pos","isSome_look_eq","key","lazyImpl_challenge_none","lazyImpl_challenge_some","lazyImpl_dec_closed","lazyImpl_dec_open","lazyImpl_enc","le_refl","look_eq_of_hitStar","look_none","look_some","one_div","ovr_apply","ovr_init","prob_bind","prob_eq_expect","prob_eq_zero_of_allOutputs","prob_pure","reduceIte","simulate_pure","simulate_query","xorPerm_apply","zero_add"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Collision

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

end TCSlib.Cryptography.Composability.PRFGame
