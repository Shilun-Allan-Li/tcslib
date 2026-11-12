import TCSlib.Cryptography.Pseudorandom.NextBit
open Lean Elab Command

namespace TCSlib.Cryptography
open Complexity Turing Finset

def idsToCheck : List String := ["A","Ensemble.pseudorandom_iff_prgAdv","Ensemble.uniform_X","Equiv.cast_apply","Equiv.prodCongr_apply","Equiv.refl_apply","List.drop_left'","List.getElem?_ofFn","List.head?_drop","List.headD_eq_head?","List.length_replicate","List.length_singleton","List.ofFn_fin_append","List.take_left'","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.coins_ofPolyTime","NUPPT.distinguisherL_eq","NUPPT.distinguisher_eq","NUPPT.inAdvice_eq","NUPPT.inArg_eq","NUPPT.inCoins_eq","NUPPT.inParam_eq","NUPPT.layout_eq","NUPPT.predictor_eq","NUPPT.runAtL_eq","NUPPT.runAtL_ofPolyTime","NUPPT.runAt_eq","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","Prod.map_fst","Prod.map_snd","abs_of_nonneg","abs_zero","acceptProb_coins_equiv","acceptProb_def","cast_cast","cast_eq","dif_pos","distAdv_def","div_div","h","h0","hA","hDm","hadv","hc","headD_drop_ofFn","hkn","hofn","hprob","hrel","hspec","i.isLt","id_eq","k","length_pairEncode","nextBitDist_eq","nextBitPred_eq","nextBitProb_eq","nextBitProb_id","ofFn_completePrefix","ofFn_prefixOf","pairFstD_pairEncode","pairSndD_pairEncode","prgAdv_eq","prgAdv_nextBitDist","uprob_comp_equiv"]
def scannedModule : Name := `TCSlib.Cryptography.Pseudorandom.NextBit

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

end TCSlib.Cryptography
