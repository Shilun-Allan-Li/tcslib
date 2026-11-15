import TCSlib.Cryptography.Randomness.Learning
open Lean Elab Command

namespace TCSlib.Cryptography.Randomness
open Complexity Turing TCSlib.Cryptography TCSlib.LearningTheory.PAC TCSlib.InformationTheory

def idsToCheck : List String := ["LearnPRF.firstBit_eq","LearnPRF.gameProb_eq","LearnPRF.learnerFn_eq","LearnPRF.predictSuccess_eq_uprob","PolyExpr.eval_add","PolyExpr.eval_const","abs_abs","abs_of_nonneg","distAdv_def","div_eq_mul_inv","div_le_div_iff₀","div_lt_iff₀","encodeSample_eq","hB","hC","hFE","hL","hQ","hreal","inv_pow","learnerOf_eq","negligible_iff","pow_one","predictAdv_eq","prfAdv_def","prfConcept","prfConcept_eq","show"]
def scannedModule : Name := `TCSlib.Cryptography.Randomness.Learning

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

end TCSlib.Cryptography.Randomness
