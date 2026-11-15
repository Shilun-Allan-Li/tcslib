import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation
open Finset Complexity Turing TCSlib.Cryptography
open TCSlib.Cryptography.SecureComputation.ComposeProb
open TCSlib.Cryptography.SecureComputation.HybridProtocol

def idsToCheck : List String := ["BinArith.eqW_pairEncode","Fintype.card_fin","Functionality.idealA_eq","Functionality.idealB_eq","Functionality.realA_eq","Functionality.realB_eq","H.inA_val","H.inB_val","HardcoreBit.pushesUniform_eval","List.length_ofFn","abs_le","acceptProb_test","card_univ","decide_eq_true_iff","decide_true","dif_pos","distAdv_def","goodRuns_iff","h1","h2","inA_eq","inB_eq","nsmul_eq_mul","pairSndD_pairEncode","sum_const","uprob_prod"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct

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
