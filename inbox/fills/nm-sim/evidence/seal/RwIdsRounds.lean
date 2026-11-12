import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Explicit readings of the nm-sim fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["EnsembleLemmas.ofFn_coinsEquiv","EnsembleLemmas.padL_eq","Equiv.prodCongr_apply","Equiv.refl_apply","Equiv.trans_apply","Fin.coe_castAdd","Fin.coe_natAdd","InteractiveHandler.call_eq","InteractiveHandler.finish_eq","InteractiveHandler.impl_apply","InteractiveHandler.input_eq","List.getD_append","List.getD_append_right","List.length_append","List.length_ofFn","List.nil_append","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","NUPPT.coinLen_eq","NUPPT.coinsEquivPoly_ofFn","Nat.sub_add_comm","Nat.zero_add","OracleComp.pure_bind","OracleComp.query_bind","PolyExpr.eval_add","Prod.map_fst","Prod.map_snd","and_self","bitCodec_encodeEntry","buildComp_of_ret","buildComp_succ_of_query","h","hlog","hp","hrun","hrun₀","hrun₁","hu","hv","h₁","h₂","if_neg","if_pos","ofFn_padFin_eq_take","padFin_apply","pairFstD_pairEncode","pairSndD_pairEncode","rdAns","rdIdx","rdLog","rdQuery","rdState","rdU","rdW","rdZ","seedEquiv","seedEquivPoly","simulate_pure","simulate_query"]

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
