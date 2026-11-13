import TCSlib.Cryptography.Games.Efficiency.OracleBridge
open Lean Elab Command

namespace TCSlib.Cryptography.Games
open Complexity Turing
open Complexity Turing
open TCSlib.Cryptography.Games.EffFill

def idsToCheck : List String := ["Fin.fin_one_eq_zero","Fin.val_zero","Function.iterate_succ_apply'","GGMRed.pairEncode_append_right","List.flatMap_cons","List.flatMap_eq_nil_iff","List.flatMap_map","List.length_cons","List.length_map","List.length_ofFn","List.map_append","List.map_cons","List.map_nil","List.map_singleton","List.nil_append","List.ofFn_succ","List.ofFn_zero","List.range_succ_eq_map","List.replicate_zero","List.tail_cons","List.tail_drop","List.tail_nil","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","OracleComp.evalFn_pure","OracleComp.evalFn_query","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_var","QueryTree.eval_query","QueryTree.eval_ret","bitCodec_encodeEntry","bridgePost_eq","bridgePre_encodeHist","bridgePre_eq","buildComp_succ_of_query","buildComp_succ_of_ret","buildComp_zero_of_query","buildComp_zero_of_ret","buildTree_succ_of_query","buildTree_succ_of_ret","buildTree_zero_of_query","buildTree_zero_of_ret","decide_eq_false","decide_eq_true","decide_eq_true_eq","decodeOracleMove_pairEncode_false_of_length_ne","decodeOracleMove_true_two","encodeHist_cons","encodeHist_nil","h","h'","h0","ha","hf","hh","hit","hq","hr","hstep","hstep_nil","hxe","id_eq","if_neg","if_pos","ih","iterEmit_eq","length_pairEncode","logHist_eq","pairFstD_pairEncode","pairSndD_pairEncode","relabelEmit_eq","relabelN_encodeHist","relabelN_eq","relabelN_eq_iterEmit","relabelN_nil","relabelN_succ","relabel_eq","relabel_eq_iterEmit","zeroBits_apply"]
def scannedModule : Name := `TCSlib.Cryptography.Games.Efficiency.OracleBridge

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

end TCSlib.Cryptography.Games
