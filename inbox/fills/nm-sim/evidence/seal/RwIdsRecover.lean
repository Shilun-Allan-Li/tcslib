import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Explicit readings of the nm-sim fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Recover.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open NMCCA2 (guessBit guessBit_eq guessBit_valid guessBit_refused)

def idsToCheck : List String := ["Bool.false_eq_true","EnsembleLemmas.padL_eq","Function.comp_apply","List.append_assoc","List.append_nil","List.drop_left'","List.drop_one","List.eq_replicate_iff","List.flatten_append","List.flatten_cons","List.flatten_flatten","List.flatten_nil","List.length_append","List.length_drop","List.length_flatten","List.length_map","List.length_range","List.length_replicate","List.map_append","List.map_congr_left","List.map_cons","List.map_const'","List.map_flatten","List.map_map","List.map_nil","List.mem_cons","List.mem_range","List.not_mem_nil","List.ofFn_const","List.sum_replicate","List.tail_cons","List.take_left'","NUPPT.Uniform.runAt_eq","NUPPT.advInput_eq","NUPPT.coins_ofPolyTime","NUPPT.distinguisherL_eq","NUPPT.inAdvice_layout","NUPPT.inArg_layout","NUPPT.inCoins_layout","NUPPT.inParam_layout","NUPPT.layout_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAtL_ofPolyTime","NUPPT.runAt_coinsCongr","NUPPT.runAt_eq","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","bitG_eq","chunkMap_flatten","ctxSt_eq","decide_false","encBit_eq","encF_eq","encPair_eq","entF_eq","entryL_drop_one","entryL_eq","guessBit_eq","h","h1","h2","h3","hB","hE","hP","hW","ha","haP","hbits","hc","hcs","hctx","hdec","henc","heq","hf","hfdef","hfl","hg","hlay","hmP","hnil","hv","hvdef","hz","hω","hℓ","if_neg","if_pos","ih","length_entryL","length_flatten_map_range","map_chunkAt_flatten","nmLen_eval","nmOutL_eq","nmOutput_eq_entryTails","nmOutput_flatten","ofFn_zeroBits","or_false","pairFstD_pairEncode","pairSndD_pairEncode","recDist","recFun","recView_eq","smul_eq_mul","this"]

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
