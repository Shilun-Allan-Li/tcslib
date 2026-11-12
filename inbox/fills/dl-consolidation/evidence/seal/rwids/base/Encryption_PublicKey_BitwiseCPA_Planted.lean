import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Planted
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.BitwiseSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["Bool.false_eq_true","Fin.coe_castLE","Fin.val_mk","Function.comp_apply","List.cons_append","List.drop_left'","List.drop_succ_cons","List.drop_zero","List.flatten_cons","List.getElem_drop","List.getElem_ofFn","List.getElem_take","List.headD_cons","List.length_append","List.length_cons","List.length_drop","List.length_ofFn","List.length_replicate","List.length_take","List.nil_append","List.ofFn_succ","List.take_left'","NUPPT.runAt_eq","PolyExpr.eval_var","blockEncFun_flatten","blockState_eq","coinBlock_drop","coinBlock_ofFn_coinBlocks","drop_ofFn_flatten","encodeList_ofFn_split","flatten_ofFn_singleton","h1","headD_drop","hi","hidx","if_false","if_neg","if_true","ih","length_pairEncode","ofFn_const_of_eq_one","padCt_eq","pairFstD_pairEncode","pairSndD_pairEncode","plantAns_eq","plantOut_eq","plantTuple_eq","seedIn_eq","take_ofFn_flatten"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Planted

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

end TCSlib.Cryptography.Composability.BitwiseSim
