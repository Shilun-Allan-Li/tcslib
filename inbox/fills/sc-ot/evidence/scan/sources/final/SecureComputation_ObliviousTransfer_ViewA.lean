import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewA
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.OT
open Complexity Turing TCSlib.Cryptography

def idsToCheck : List String := ["Bool.false_eq_true","Collection.decD_eq_some_iff","Collection.index_eq","Equiv.prodComm_apply","Functionality.idealA_eq","Functionality.realA_eq","List.drop_left'","List.headD_cons","List.length_replicate","List.take_left'","NUPPT.runAt_eq","Option.getD_some","Prod.fst_swap","Prod.snd_swap","Protocol.viewP_eq","Strategy.encodeMsgs_cons","Strategy.encodeMsgs_nil","T.f_perm","View.encode_mk","acceptProb_comp_equiv","add_zero","distAdv_def","eA","eC","hev","hout","hx","idealA_simACoins","if_false","if_true","isSimA_iff","ofFn_eq_inB1","ofFn_f_snd","ofFn_inA2","ofFn_inB1","pairFstD_pairEncode","realA_realCoins","realCoins_symm_fst_ofFn","realCoins_symm_snd_ofFn","receiverNext_single","simACoins_symm_ofFn","simAView_layout","transcriptWith_isOT","uprob_prod","zero_add"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewA

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
