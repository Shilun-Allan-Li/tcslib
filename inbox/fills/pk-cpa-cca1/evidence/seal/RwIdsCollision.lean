import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
open Lean Elab Command

/-! Explicit readings of the pk-cpa-cca1 fill in `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Collision.lean`: every identifier the added lines pass
to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in
the file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.PRFGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","Bool.false_and","Bool.false_eq_true","Bool.false_or","Bool.not_eq_true","Bool.or_false","Bool.true_or","List.getElem_zipWith","List.length_map","List.length_nil","List.length_ofFn","List.length_singleton","List.lookup_cons","List.lookup_nil","List.map_cons","Nat.cast_one","Nat.cast_zero","Option.getD_none","Option.isSome_none","Option.map_none","abs_le","addPt_eq","addPt_eq_of","ctOf_eq","ctOf_xorPerm","decide_eq_false_iff_not","div_eq_mul_one_div","expect_add","expect_bind","expect_const","expect_pure","expect_sample_comm","flag_addPt","h","hK","hY","hatk","hb","hcard","hi2","hitStar_none","hitStar_some","hml","hs","hv","hx","h₀","h₁","if_false","if_neg","if_pos","isSome_look_eq","key","lazyImpl_challenge_none","lazyImpl_challenge_some","lazyImpl_dec_closed","lazyImpl_dec_open","lazyImpl_enc","le_refl","look_eq_of_hitStar","look_none","look_some","one_div","ovr_apply","ovr_init","prob_bind","prob_eq_expect","prob_eq_zero_of_allOutputs","prob_pure","reduceIte","simulate_pure","simulate_query","xorPerm_apply","zero_add"]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let n := s.toName
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

end TCSlib.Cryptography.Composability.PRFGame
