import TCSlib.Cryptography.Authentication.MAC.FromPRF.Handler
open Lean Elab Command

namespace TCSlib.Cryptography.Authentication.PRFMAC
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rS rI rX rL rAns finA)
open TCSlib.Cryptography.Composability.NMSim (chunkMap chunkMap_flatten polyTimeComputable_chunkMap)

def idsToCheck : List String := ["Bool.false_and","Bool.true_and","Collection.ofFn_padFin_of_le","Function.comp_apply","InteractiveHandler.finA_finInput","InteractiveHandler.finish_eq","InteractiveHandler.rAns_eq","InteractiveHandler.rAns_input","InteractiveHandler.rI_input","InteractiveHandler.rL_finInput","InteractiveHandler.rL_input","InteractiveHandler.rS_finInput","InteractiveHandler.rS_input","InteractiveHandler.rU_finInput","InteractiveHandler.rU_input","InteractiveHandler.rX_input","List.append_assoc","List.cons_append","List.eq_of_mem_replicate","List.flatten_append","List.flatten_cons","List.flatten_eq_nil_iff","List.flatten_nil","List.flatten_replicate_replicate","List.length_append","List.length_cons","List.length_nil","List.length_ofFn","List.length_replicate","List.length_singleton","List.length_take","List.map_cons","List.map_nil","List.nil_append","List.replicate_succ","List.take_append","List.take_of_length_le","List.take_replicate","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","Nat.min_eq_left","Nat.sub_mul","Nat.zero_mul","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","bitCodec_encodeEntry","blockLen","blockLen_eval","blocks_cons","blocks_eq","buildComp_succ_of_query","chunkMap_flatten","decide_eq_false","decide_eq_true","hB","hans","hcut","hflat","hitEmit","hitsOf","hlog","hmin","hmu","hp","hrun₀","hrun₁","hx","if_neg","if_pos","ih","length_blocks","macFin","macHandler_finCall","macHandler_init","macHandler_outLen","macHandler_perCall","macHandler_stateLen","macHandler_stateLen_eval","macRun","macStLen","macStLen_eval","macState_eq","msgOf","ofFn_macState","ofFn_padFin_of_length","padFin_def","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","sigOf","zeroBits_apply"]
def scannedModule : Name := `TCSlib.Cryptography.Authentication.MAC.FromPRF.Handler

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

end TCSlib.Cryptography.Authentication.PRFMAC
