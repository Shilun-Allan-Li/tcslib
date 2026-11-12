import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Explicit readings of the nm-sim fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Reduction.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open NMCCA2 (finU finZ finW finA fields_finInput polyTimeComputable_finFields)

def idsToCheck : List String := ["Bool.false_eq_true","EnsembleLemmas.length_padL","Function.comp_apply","GGMRed.ofFn_padFin_of_length","InteractiveHandler.advInput_eq","List.append_nil","List.drop_left'","List.flatten_cons","List.length_append","List.length_drop","List.length_ofFn","List.length_replicate","List.length_singleton","List.map_cons","List.map_map","List.mem_range","List.take_left'","NUPPT.runAtL_eq_output_layout","NUPPT.runAt_eq","Nat.add_sub_cancel_left","Nat.add_zero","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","QueryImpl.comp_apply","altMsg_eq","chalHandler_advIn","chalHandler_finRun","chalHandler_impl_dec","chalHandler_impl_none","chalHandler_impl_some","chalHandler_outLen","chalHandler_seedLen","chalHandler_stateLen_eval","chunkMap_flatten","drawWith_eq","encBit_eq","encF_eq","encPair_eq","encWith_eq","finMsg_eq","finSt_finInput","h0","hA","hH","hQ","hU","hW","hY","hZ","ha","haP","hans","hbits","hd","hdraw","histWith_eq","hm","hm'","hmP","hpl","hq","hs","hx'","if_neg","if_pos","ih","length_chunkAt","length_encBit","length_flatten_map_const","length_flatten_map_range","length_nmOutL","nmAbs_none","nmAbs_some","nmFin_eq","nmLen","nmLen_eval","nmOutL_eq","nmPair_eq","nmParams_advIn","nmParams_ansH","nmParams_ansY","nmParams_finRun","nmParams_j","nmParams_outLen","nmParams_outLen_eval","nmParams_qry","nmParams_seedLen","nmSeed","nmSeed_ofFn","ofFn_drawWith_half","ofFn_padFin_eq_padL","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","rImpl_dec_cpa","rImpl_none_eager","rImpl_none_lazy","rImpl_some","rdAns_input","seedEquivPoly_ofFn","seedEquiv_ofFn","seedIn_eq","simMsg_eq","simulate_pure","simulate_query","snmDin_one","snmDout_one","stParam_eq","take_eq_flatten_chunkAt"]

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
