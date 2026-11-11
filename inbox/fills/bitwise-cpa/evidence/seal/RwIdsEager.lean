import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA
open Lean Elab Command

/-! Explicit readings of the bitwise-cpa fill in `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Eager.lean`: every identifier the added lines pass to
`rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.BitwiseSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim ProbComp

def idsToCheck : List String := ["Bool.false_and","Bool.false_eq_true","FixedLengthScheme.decOpen_cpa","NUPPT.coinsCongr_ofFn","NUPPT.runAt_eq","OracleComp.bind_assoc","OracleComp.pure_bind","PublicKeyScheme.padded_enc","S.indImpl_dec_onSpec","chRun_pure","chRun_query_one_none","chRun_query_one_some","chRun_query_zero","expect_bind","expect_pure","expect_sample_prod","h0","hc","hd","he","hmap","hnew","hrep","ht","if_false","ih","padEnc_coins","runAt_padEnc","simulate_pure","simulate_query"]

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

end TCSlib.Cryptography.Composability.BitwiseSim
