import TCSlib.Cryptography.Randomness.Learning.Random
open Lean Elab Command

namespace TCSlib.Cryptography.Randomness.LearnPRF
open Complexity TCSlib.Cryptography TCSlib.LearningTheory.PAC Finset

def idsToCheck : List String := ["Bool.not_not","Finset.card_singleton","Finset.card_univ","Finset.filter_eq","Finset.sum_const","Finset.sum_sub_distrib","Fintype.card_bool","Fintype.card_fin","Fintype.card_fun","Function.Involutive.coe_toPerm","Function.update_eq_self","Function.update_idem","Function.update_of_ne","Function.update_self","List.headD_cons","List.ofFn_succ","Nat.cast_one","Nat.cast_pow","Nat.cast_two","abs_div","abs_le","abs_of_pos","abs_zero","firstBit_eq","firstBit_flip0","firstBit_of_pos","flip0_eq","flip0_flip0","flipAt_eq","gameProb_eq","h2","hgame","hhalf","hj","hl","hp","hσ","if_neg","if_pos","label_apply","nsmul_eq_mul","sub_div","sub_self","uexp_def","uprob_comp_equiv","uprob_eq_card_filter","uprob_eq_point","uprob_eq_uexp","uprob_flip_half","uprob_not","uprob_prod"]
def scannedModule : Name := `TCSlib.Cryptography.Randomness.Learning.Random

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
