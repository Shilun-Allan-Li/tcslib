import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
open Lean Elab Command

namespace TCSlib.Cryptography
open Complexity Turing Finset

def idsToCheck : List String := ["Equiv.coe_addRight","Equiv.coe_refl","Equiv.prodAssoc_apply","Equiv.prodCongr_apply","Fin.tail_def","Finset.sum_congr","Finset.sum_const","Fintype.card_bool","Fintype.card_fin","Fintype.card_fun","Function.not_injective_iff","MultiMsg.card_filter_lt_pairs","MultiMsg.uprob_eq_pair","Pi.add_apply","Prod.map_fst","Prod.map_snd","QueryTree.boundedBy_query_succ","QueryTree.eval_query","QueryTree.eval_ret","S","abs_sub_comm","acceptProb_def","acceptProb_oracleDist_multiMsgAdv","chainTree","distAdv_def","eval_chainTree","h","h12","h34","h56","hS","ha","hb","id_eq","mul_one_div","multiMsgAdv","nsmul_eq_mul","oracleDist_apply","otpEnc","prfAdv_def","show","sum_empty","uexp_def","univ_eq_empty","uprob_comp_equiv","uprob_prod","zero_div"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid

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

end TCSlib.Cryptography
