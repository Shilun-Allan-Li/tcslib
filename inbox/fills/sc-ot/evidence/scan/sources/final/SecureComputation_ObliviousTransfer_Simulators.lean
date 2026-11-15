import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Simulators
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.OT
open Complexity Turing TCSlib.Cryptography

def idsToCheck : List String := ["Collection.index_eq","Equiv.prodCongr_apply","Equiv.prodCongr_symm","Equiv.refl_apply","Equiv.refl_symm","Equiv.symm_trans_apply","List.append_assoc","List.append_nil","List.drop_left'","List.length_append","List.length_nil","List.length_ofFn","List.length_replicate","List.nil_append","List.ofFn_congr","List.ofFn_succ","List.ofFn_zero","List.take_left'","NUPPT.Uniform.advice_eq","NUPPT.coinLen_eq","NUPPT.inArg_layout","NUPPT.inCoins_layout","NUPPT.inParam_layout","NUPPT.runAtL_eq_output_layout","NUPPT.runAt_eq","PolyExpr.eval_add","PolyExpr.eval_const","Prod.map_fst","Prod.map_snd","Strategy.coinLen_eq","h","hA","hc","hi","hs","h₀","h₁","h₂","isOT_iff","isSimA_iff","isSimB_iff","length_ofFn_coins","ofFn_inB1","ofFn_splitCoins_symm","otFunctionality_f_snd_apply","otFunctionality_inA","otFunctionality_inB","otFunctionality_outA","otFunctionality_outB","simACoins","simAView_eq","simBCoins","simBView_eq","simIndex_eq","simIndex_layout","simSampled_eq","simSeg_eq","simZbit_eq","simZpair_eq","splitLen_symm_ofFn"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Simulators

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

end TCSlib.Cryptography.SecureComputation.OT
