import TCSlib.Cryptography.Games.Efficiency
open Lean Elab Command

namespace TCSlib.Cryptography.Games
open Complexity Turing
open TCSlib.Cryptography.Games.PolyHandler
open TCSlib.Cryptography.Games.InteractiveHandler

def idsToCheck : List String := ["EffFill.fixLen_nil","EffFill.iCall_eq","EffFill.iFinish_eq","EffFill.iImpl_apply","EffFill.iRaw_spec","EffFill.iX_eq","EffFill.logHist_eq","EffFill.ofFn_getD_decodeFin","InteractiveHandler.advInput_eq","InteractiveHandler.call_eq","InteractiveHandler.finInput_eq","InteractiveHandler.finish_eq","InteractiveHandler.impl_apply","InteractiveHandler.input_eq","List.length_ofFn","List.map_nil","NUPPT.runAt_coinsCongr","NUPPT.runAt_eq","NUPPT.toCompOn_eq","NUPPT.toComp_eq","NUPPT.toOracleAdversary_eq","Option.getD_some","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyHandler.advInput_eq","PolyHandler.answer_of_pairDecode_eq_none","PolyHandler.answer_of_pairDecode_eq_some","PolyHandler.input_eq","PolyHandler.result_eq","answer","answer_of_pairDecode_eq_some","bitCodec_decodeMove","bitCodec_timeout","decodeFin_ofFn","eq_pairEncode_of_pairDecode","h","hA'","hB'","hfin","himpl","hnext","hraw","hφ","id_eq","length_pairEncode","ofFn_zeroBits","pairDecode_pairEncode","pairFstD_of_pairDecode_eq_none","pairFstD_pairEncode","pairSndD_of_pairDecode_eq_none","pairSndD_pairEncode","seedIn_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Games.Efficiency

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> pure []
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
