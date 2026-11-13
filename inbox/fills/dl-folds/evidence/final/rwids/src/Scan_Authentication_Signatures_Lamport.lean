import TCSlib.Cryptography.Authentication.Signatures.Lamport
open Lean Elab Command

namespace TCSlib.Cryptography.Authentication
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.PrivateKeyScheme (encodeList)

def idsToCheck : List String := ["Bool.true_and","Function.comp_apply","Function.comp_def","List.append_nil","List.cons.injEq","List.flatMap_def","List.flatten_cons","List.headD_cons","List.length_append","List.length_nil","List.length_ofFn","List.length_replicate","List.map_ofFn","List.ofFn_succ","List.replicate_zero","NUPPT.advInput_eq","NUPPT.coins_ofPolyTimeUniform","NUPPT.inArg_eq","NUPPT.inArg_layout","NUPPT.inCoins_eq","NUPPT.inCoins_layout","NUPPT.inParam_eq","NUPPT.inParam_layout","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","Nat.sub_self","Nat.succ_mul","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","and_true","atParam_eq","blockEncFun_eq","blockEncFun_ofFn","blockEncFun_spec","blockList_ofFn","blockState_eq","coinBlock_flatten","coinBlock_flatten_ofFn","decListFun_eq","decListFun_pairSndD","decListFun_spec","decide_eq_true_eq","decide_true","encodeList_eq_flatMap","h","hflat","hg","hpad","hs","hx","hx'","hy","hρ","hσ","lamportEvalEmit","lamportGen","lamportGenFun","lamportGenFun_eq","lamportHalf","lamportPairEmit","lamportPkBlock","lamportPkEmit","lamportSelEmit","lamportSign","lamportSignFun","lamportSignFun_eq","lamportVerFun","length_flatten_ofFn","length_pairEncode","pairFstD_pairEncode","pairSndD_pairEncode","runAt_lamportGen","runAt_lamportSign","show"]
def scannedModule : Name := `TCSlib.Cryptography.Authentication.Signatures.Lamport

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

end TCSlib.Cryptography.Authentication
