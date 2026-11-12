import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Explicit readings of the nm-sim fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Challenge.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["EnsembleLemmas.padL_eq","Function.comp_apply","GGMRed.ofFn_padFin_of_length","List.drop_one","List.getD_eq_default","List.getD_eq_getElem","List.getElem_replicate","List.headD_cons","List.length_append","List.length_cons","List.length_ofFn","List.length_replicate","List.replicate_succ","List.tail_cons","Nat.add_assoc","Nat.add_comm","Option.isSome_none","Option.isSome_some","P.ansH_len","P.ansY_len","P.qry_len","PolyExpr.eval_add","PolyExpr.eval_const","chalHandler_impl_dec","chalHandler_impl_none","chalHandler_impl_some","chalHandler_perCall","chalHandler_stateLen","chalHandler_stateLen_eval","chalRun_eq","chalState_none","chalState_some","hH","hI","hI₀","hI₁","hL₀","hL₁","hQ₁","hS","hS₀","hS₁","hU","hU₀","hU₁","hW₁","hY","hans","headD_ofFn_chalState","hq","hx","if_neg","impl_of_query","impl_of_ret","ofFn_chalState_none","ofFn_chalState_some","ofFn_zeroBits","padFin_apply","padFin_ofFn","padFin_replicate_false","pairFstD_pairEncode","pairSndD_pairEncode","snmDin_one","snmDout_one","snmDout_zero","zeroBits_apply"]

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
