import TCSlib.Cryptography.Randomness.Learning.Law
open Lean Elab Command

namespace TCSlib.Cryptography.Randomness.LearnPRF
open Complexity Turing TCSlib.Cryptography TCSlib.InformationTheory TCSlib.LearningTheory.PAC

def idsToCheck : List String := ["Equiv.prodCongr_apply","Equiv.refl_apply","Equiv.trans_apply","Fin.init_snoc","Fin.snoc_castSucc","Fin.snoc_init_self","Fin.snoc_last","FinDist.iid_apply","FinDist.uniform_apply","Finset.card_univ","Finset.prod_const","Fintype.card_fin","Fintype.card_fun","Nat.cast_pow","Prod.map_apply","Rejection.uniform_probTrue","Rejection.uniform_prod","acceptProb_def","div_eq_mul_inv","gameProb_eq","hlab","hφ","iid_uniform","inv_pow","learnerFn_eq","oracleDist_apply","predictSuccess_eq","snocEquiv_apply","trialDist_eq","uprob_comp_equiv","uprob_eq_card_filter"]
def scannedModule : Name := `TCSlib.Cryptography.Randomness.Learning.Law

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

end TCSlib.Cryptography.Randomness.LearnPRF
