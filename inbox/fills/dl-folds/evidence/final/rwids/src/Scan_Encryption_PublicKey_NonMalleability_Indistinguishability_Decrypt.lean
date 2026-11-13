import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Decrypt
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.NMCCA2
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
open TCSlib.Cryptography.Games.InteractiveHandler (rU_finInput rZ_finInput rW_finInput rL_finInput finA_finInput polyTimeComputable_rU polyTimeComputable_rZ polyTimeComputable_rW polyTimeComputable_rL polyTimeComputable_finA)
open AdaptiveCPA (acDin acDout acDin_zero acDout_zero)

def idsToCheck : List String := ["EnsembleLemmas.padL_eq","Function.comp_apply","InteractiveHandler.advInput_eq","InteractiveHandler.finish_eq","List.flatMap_def","List.flatMap_map","List.length_flatMap","List.length_map","List.length_range","List.length_replicate","List.length_singleton","List.map_append","List.map_cons","List.map_const'","List.map_nil","List.range_succ","List.range_zero","List.sum_replicate","NUPPT.layout_eq","Nat.add_zero","OracleComp.pure_bind","PolyExpr.eval_const","PrefixByLength.drop_def","acDin_zero","ansRead_eq","bitCodec_encodeEntry","buildComp_succ_of_query","buildComp_zero_of_ret","cntRead_eq","dCnt","dCt","dFin","dIn","decBlock_eq","decHandler","decHandler_finCall","decHandler_outLen","decide_eq_false","fwdHandler_advIn","fwdHandler_finCall","fwdHandler_finRun","fwdHandler_outLen","fwdHandler_perCall","fwdHandler_seedLen","h0","hA","hCt","hIn","hL","hO","hU","hW","hZ","hc","hctl","hfin","hh","hhist","hout","hw","if_neg","if_pos","length_logEmit_cntRead","logEmit_ansRead","logEmit_encodeLog","mul_one","ofFn_padFin_eq_take","pairFstD_nil","pairFstD_pairEncode","pairSndD_of_pairDecode_eq_none","pairSndD_pairEncode","seedIn_eq","simulate_pure","simulate_query","smul_eq_mul"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Decrypt

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

end TCSlib.Cryptography.Composability.NMCCA2
