import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Reduction
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
open TCSlib.Cryptography.EnsembleLemmas (seedEquiv seedEquivPoly seedEquiv_ofFn seedEquivPoly_ofFn ofFn_padFin_eq_padL)
open TCSlib.Cryptography.Games.InteractiveHandler (rU_input rZ_input rW_input rX_input rAns_input rU_finInput rZ_finInput rW_finInput rS_finInput finA_finInput polyTimeComputable_rU polyTimeComputable_rZ polyTimeComputable_rW polyTimeComputable_rS polyTimeComputable_rX polyTimeComputable_rAns polyTimeComputable_finA)

def idsToCheck : List String := ["Bool.false_eq_true","EnsembleLemmas.length_padL","Function.comp_apply","InteractiveHandler.advInput_eq","List.append_nil","List.drop_left'","List.flatten_cons","List.length_append","List.length_drop","List.length_ofFn","List.length_replicate","List.length_singleton","List.map_cons","List.map_map","List.mem_range","List.take_left'","NUPPT.runAtL_eq_output_layout","NUPPT.runAt_eq","Nat.add_sub_cancel_left","Nat.add_zero","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","QueryImpl.comp_apply","altMsg_eq","chalHandler_advIn","chalHandler_finRun","chalHandler_impl_dec","chalHandler_impl_none","chalHandler_impl_some","chalHandler_outLen","chalHandler_seedLen","chalHandler_stateLen_eval","chunkMap_flatten","drawWith_eq","encBit_eq","encF_eq","encPair_eq","encWith_eq","finMsg_eq","h0","hA","hH","hQ","hU","hW","hY","hZ","ha","haP","hans","hbits","hd","hdraw","histWith_eq","hm","hm'","hmP","hpl","hq","hs","hx'","if_neg","if_pos","ih","length_coinBlock","length_encBit","length_flatten_map_const","length_flatten_map_range","length_nmOutL","nmAbs_none","nmAbs_some","nmFin_eq","nmLen","nmLen_eval","nmMsgs_input","nmOutL_eq","nmPair_eq","nmParams_advIn","nmParams_ansH","nmParams_ansY","nmParams_finRun","nmParams_j","nmParams_outLen","nmParams_outLen_eval","nmParams_qry","nmParams_seedLen","nmSeed","nmSeed_ofFn","ofFn_drawWith_half","ofFn_padFin_eq_padL","ofFn_padFin_of_length","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","rAns_input","rImpl_dec_cpa","rImpl_none_eager","rImpl_none_lazy","rImpl_some","rS_finInput","rU_input","reduceIte","seedEquivPoly_ofFn","seedEquiv_ofFn","seedIn_eq","simMsg_eq","simulate_pure","simulate_query","snmDin_one","snmDout_one","stParam_eq","take_eq_flatten_chunkAt"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Reduction

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> (Pure.pure [] : CoreM (List Name))
    if cands.isEmpty then IO.println s!"{s}\t-\tlocal/unresolved\t-"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some (.opaqueInfo _) => "opaque"
        | some (.inductInfo _) => "inductive"
        | some (.ctorInfo _) => "ctor"
        | some _ => "other"
        | none => "?"
      let m := modOf c
      let tag := if k == "DEF" then
          (if m == scannedModule then "own-def" else if (`TCSlib).isPrefixOf m then "FOREIGN-TCSLIB-DEF" else "core/mathlib-def")
        else k
      IO.println s!"{s}\t{c}\t{tag}\t{m}"

end TCSlib.Cryptography.Composability.NMSim
