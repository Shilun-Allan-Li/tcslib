import TCSlib.Cryptography.Randomness.Learning.Distinguisher
open Lean Elab Command

namespace TCSlib.Cryptography.Randomness.LearnPRF
open Complexity Turing TCSlib.Cryptography

def idsToCheck : List String := ["Equiv.prodCongr_apply","Equiv.refl_apply","Equiv.trans_apply","Function.comp_apply","List.length_ofFn","List.take_of_length_le","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.coins_ofPolyTimeUniform","NUPPT.inArg_eq","NUPPT.inParam_eq","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","Nat.add_zero","Pi.add_apply","PolyExpr.eval_add","PolyExpr.eval_const","Prod.map_apply","hA₁","hA₁c","hC","hCc","hlen₁","hw","hφ₀","lastLabel_tupleWord","learnIn_tupleWord","ofFn_arrowCongr_finCongr","pairFstD_pairEncode","pairSndD_pairEncode","tupleWord_eq","verdictFun_eq","zero_add_fun"]
def scannedModule : Name := `TCSlib.Cryptography.Randomness.Learning.Distinguisher

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
