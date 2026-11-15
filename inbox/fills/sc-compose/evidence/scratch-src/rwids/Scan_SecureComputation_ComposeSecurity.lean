import TCSlib.Cryptography.SecureComputation.ComposeSecurity
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography
open Compose
open TCSlib.Cryptography.SecureComputation.HybridProtocol

def idsToCheck : List String := ["Function.comp_def","H.runInputA_of_lt","H.runInputB_of_lt","List.eq_of_mem_replicate","List.length_flatten","List.length_ofFn","List.length_replicate","List.length_take","List.map_ofFn","List.mem_append","List.mem_map","List.mem_range","List.ofFn_const","List.sum_replicate","Nat.mul_zero","PolyExpr.eval_add","Protocol.transcriptWith_eq","Protocol.transcript_eq_transcriptWith","Strategy.coinLen_eq","answersRealA_eq","answersRealB_eq","compose_transcript","exec_eq_map","h","haA","haB","hmain","htA","htB","hxA","hyB","length_answersRealA","length_answersRealB","mainExec_eq","runExec_eq","runMsg_eq","slotFromA_eq","slotFromB_eq","smul_eq_mul"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity

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
