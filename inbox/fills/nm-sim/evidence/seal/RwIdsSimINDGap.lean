import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Explicit readings of the nm-sim fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimINDGap.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

def idsToCheck : List String := ["GGMRed.ofFn_padFin_of_length","List.append_assoc","List.length_ofFn","Nat.add_zero","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","accept_nmGame_eq_rImpl","copyHandler_outLen","div_eq_inv_mul","expect_add","expect_bind","expect_const","expect_const_mul","expect_pure","expect_sample_comm","expect_sample_equiv","expect_sample_halfCoins","expect_sample_prod","expect_sub","hC","hI","halfDist_blocks","halfDist_idealView_coin","hd","hhl","histImpl_coins","hr","hβ","idealAcc_eq","idealView_eq","rImpl_false_coins","realAcc_copyHandler","realAcc_eq","realAcc_half","runB_eq","simulate_copyHandler_machine"]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let s' := if s.startsWith "S." then "FixedLengthPKScheme." ++ (s.drop 2) else
      if s.startsWith "M." then "MsgSampler." ++ (s.drop 2) else
      if s.startsWith "samp." then "Complexity.NUPPT." ++ (s.drop 5) else s
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

end TCSlib.Cryptography.Composability.NMSim
