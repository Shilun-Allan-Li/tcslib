import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity
open Lean Elab Command

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

def idsToCheck : List String := ["Bool.false_eq_true","Equiv.coe_fn_mk","Fin.coe_castSucc","Fin.ext_iff","Fin.is_lt","Fin.lt_def","Fin.val_succ","Function.update_eq_self","Function.update_idem","Function.update_of_ne","Function.update_self","LWE.decisionAdvantage_eq","Nat.not_lt_zero","Nat.one_ne_zero","Regev.keygen_fst","abs_sub_comm","acceptProb_def","add_le_iff_nonpos_right","and_false","and_true","distAdv_def","evalKey_eq","false_and","hb","hc","he","hf","hij","hij'","hle","hlt","hsec","ht","hv","hybridPlant_eq","if_false","if_true","levelAssemble_eq","levelHybrid_eq","levelKey_eq","levelMsgs_eq","levelPosHybrid","levelPosHybrid_columns","levelPosHybrid_zero","levelReduction_eq","levelTerm_eq","lt_self_iff_false","nonpos_iff_eq_zero","reduction_eq","true_and","uniformKeyView_eq","uprob_comp_equiv","uprob_fst","uprob_prod","view_eq","Ψ"]
def scannedModule : Name := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity

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

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
