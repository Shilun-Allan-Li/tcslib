import TCSlib.Cryptography.Games.Efficiency
open Lean Elab Command

namespace TCSlib.Cryptography.Games
open Complexity Turing
open TCSlib.Cryptography.Games.PolyHandler
open TCSlib.Cryptography.Games.InteractiveHandler

def idsToCheck : List String := ["EffFill.fixLen_nil","EffFill.iCall_eq","EffFill.iFinish_eq","EffFill.iImpl_apply","EffFill.iRaw_spec","EffFill.iX_eq","EffFill.logHist_eq","EffFill.ofFn_getD_decodeFin","InteractiveHandler.advInput_eq","InteractiveHandler.call_eq","InteractiveHandler.finInput_eq","InteractiveHandler.finish_eq","InteractiveHandler.impl_apply","InteractiveHandler.input_eq","List.length_ofFn","List.map_nil","List.nil_append","List.ofFn_fin_append","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","NUPPT.runAt_coinsCongr","NUPPT.runAt_eq","NUPPT.toCompOn_eq","NUPPT.toComp_eq","NUPPT.toOracleAdversary_eq","Option.getD_some","OracleComp.pure_bind","OracleComp.query_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyHandler.advInput_eq","PolyHandler.answer_of_pairDecode_eq_none","PolyHandler.answer_of_pairDecode_eq_some","PolyHandler.input_eq","PolyHandler.result_eq","answer","answer_of_pairDecode_eq_some","bitCodec_decodeMove","bitCodec_encodeEntry","bitCodec_timeout","buildComp_of_ret","buildComp_succ_of_query","buildComp_succ_of_ret","buildComp_zero_of_ret","call_eq","decodeFin_ofFn","eq_pairEncode_of_pairDecode","finA","finInput_eq","finish_eq","h","hA'","hB'","hfin","himpl","hlog","hnext","hp","hraw","hs","hy","hφ","h₀","h₁","id_eq","impl_apply","input_eq","length_pairEncode","ofFn_zeroBits","pairDecode_pairEncode","pairFstD_of_pairDecode_eq_none","pairFstD_pairEncode","pairSndD_of_pairDecode_eq_none","pairSndD_pairEncode","rAns","rCnt","rI","rL","rL_input","rS","rS_input","rU","rW","rX","rZ","seedIn_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Games.Efficiency

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
