import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA
open Lean Elab Command

/-! Explicit readings of the bitwise-cpa fill in `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Planted.lean`: every identifier the added lines pass to
`rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.BitwiseSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["Bool.false_eq_true","Fin.coe_castLE","Fin.val_mk","Function.comp_apply","List.cons_append","List.drop_left'","List.drop_succ_cons","List.drop_zero","List.flatten_cons","List.getElem_drop","List.getElem_ofFn","List.getElem_take","List.headD_cons","List.length_append","List.length_cons","List.length_drop","List.length_ofFn","List.length_replicate","List.length_take","List.nil_append","List.ofFn_succ","List.take_left'","NUPPT.runAt_eq","PolyExpr.eval_var","blockEncFun_flatten","blockState_eq","coinBlock_drop","coinBlock_ofFn_coinBlocks","drop_ofFn_flatten","encodeList_ofFn_split","flatten_ofFn_singleton","h1","headD_drop","hi","hidx","if_false","if_neg","if_true","ih","length_pairEncode","ofFn_const_of_eq_one","padCt_eq","pairFstD_pairEncode","pairSndD_pairEncode","plantAns_eq","plantOut_eq","plantTuple_eq","seedIn_eq","take_ofFn_flatten"]

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
