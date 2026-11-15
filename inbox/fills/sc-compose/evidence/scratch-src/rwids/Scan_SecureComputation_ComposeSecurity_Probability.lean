import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.ComposeProb
open Finset Complexity

def idsToCheck : List String := ["abs_div","abs_le","abs_mul","abs_of_nonneg","abs_of_pos","acceptProb_def","acceptProb_eq_uexp_sections","card_univ","distAdv_def","div_le_iff₀","h","mul_assoc","mul_comm","mul_pow","nsmul_eq_mul","sub_div","sum_const","sum_sub_distrib","uexp_def","uprob_comp_equiv","uprob_fst","uprob_prod"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability

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

end TCSlib.Cryptography.SecureComputation.ComposeProb
