import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography ComposeBound
open TCSlib.Cryptography.SecureComputation.HybridProtocol
open TCSlib.Cryptography.SecureComputation.ComposeBound

def idsToCheck : List String := ["Function.comp_def","H.length_answersA","H.length_answersB","I","List.length_flatten","List.length_ofFn","List.length_replicate","List.map_ofFn","List.ofFn_const","List.sum_replicate","NUPPT.coinLen_eq","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_pow","PolyExpr.eval_var","Protocol.outP_eq","Protocol.outV_eq","Protocol.transcript_eq_transcriptWith","Protocol.viewP_eq","Protocol.viewV_eq","Strategy.coinLen_eq","View.encode_mk","answersA_eq","answersB_eq","hR","haA","haB","hc","hpA","hpB","ht","length_ilayout","length_pairEncode","privA_eq","privB_eq","smul_eq_mul"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths

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

end TCSlib.Cryptography.SecureComputation
