import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
open Lean Elab Command

/-! Explicit readings of the padded-cpa fill in `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean`: every identifier the added lines pass to
`rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.ChallengeSim
open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["Bool.false_and","Bool.false_eq_true","Bool.true_and","Equiv.sum_comp","Finset.mul_sum","Fintype.card_congr","Fintype.card_prod","Fintype.card_unique","Fintype.sum_prod_type","Fintype.sum_unique","List.length_ofFn","Nat.cast_mul","Option.some.injEq","bne_self_eq_false","chRun_query_one_none","chRun_query_one_some","chRun_query_zero","expect_const","expect_const_mul","expect_sample","expect_sample_equiv","expect_sample_prod","expect_sub","firstQ_pure","firstQ_query_one","firstQ_query_zero","h","hf","hneg","ht","hx","if_false","ih","mul_inv","neg_one_mul","rfl","sub_eq_add_neg","sub_self"]

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

end TCSlib.Cryptography.Composability.ChallengeSim
