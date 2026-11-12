import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Explicit readings of the nm-sim fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Hybrid.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["Bool.false_and","Bool.false_eq_true","Fin.coe_castAdd","FixedLengthScheme.decOpen_cpa","Function.comp_apply","List.append_assoc","List.drop_append_of_le_length","List.drop_drop","List.drop_left'","List.drop_of_length_le","List.drop_zero","List.flatten_append","List.flatten_cons","List.flatten_nil","List.flatten_singleton","List.getElem_drop","List.getElem_map","List.getElem_ofFn","List.getElem_range","List.getElem_take","List.length_append","List.length_cons","List.length_drop","List.length_map","List.length_nil","List.length_ofFn","List.length_range","List.length_replicate","List.length_take","List.map_append","List.map_cons","List.map_map","List.map_nil","List.map_singleton","List.nil_append","List.ofFn_add","List.ofFn_inj","List.range_succ","List.range_succ_eq_map","List.range_zero","List.take_add","List.take_left'","List.take_zero","Nat.add_comm","Nat.add_zero","Nat.mul_comm","Nat.succ_mul","Nat.zero_mul","PolyExpr.eval_add","PolyExpr.eval_const","S.inLens_one","S.inLens_zero","S.outLens_one","S.outLens_zero","chunkAt_eq","entryL_eq","finProdFinEquiv_apply_val","hg","histImpl_eq","hsub","hv","hybAcc_eq","if_neg","if_pos","ih","length_flatten_map_range","rImpl_dec","rImpl_eq_of_msgLen_eq_zero","rImpl_false_coins","rImpl_none_eager","rImpl_none_lazy","realAcc_eq","snmDin_one","snmDin_zero","snmDout_one","snmDout_zero"]

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
