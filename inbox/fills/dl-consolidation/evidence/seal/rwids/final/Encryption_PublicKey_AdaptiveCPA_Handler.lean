import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.AdaptiveCPA
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rCnt)

def idsToCheck : List String := ["Collection.ofFn_padFin_of_le","EnsembleLemmas.ofFn_padFin_eq_padL","Equiv.arrowCongr_apply","Equiv.refl_apply","Equiv.refl_symm","Equiv.trans_apply","Fin.val_one","Function.comp_apply","GGMRed.pairEncode_append_right","InteractiveHandler.advInput_eq","InteractiveHandler.call_eq","InteractiveHandler.finInput_eq","InteractiveHandler.finish_eq","InteractiveHandler.impl_apply","InteractiveHandler.rCnt_input","InteractiveHandler.rI_input","InteractiveHandler.rL_input","InteractiveHandler.rS_input","InteractiveHandler.rU_input","InteractiveHandler.rW_input","InteractiveHandler.rX_input","InteractiveHandler.rZ_input","List.cons.injEq","List.headD_nil","List.length_ofFn","List.length_replicate","List.nil_append","List.ofFn_fin_append","List.replicate_one","List.replicate_succ","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","NUPPT.Uniform.runAt_eq","NUPPT.advInput_eq","NUPPT.coinsEquivPoly_symm_ofFn","OracleComp.pure_bind","OracleComp.query_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PrefixByLength.drop_def","acDout_zero","acFin","acHState_eq","acHandler_advIn","acHandler_outLen","acHandler_perCall","acRun","acStLen_eq","acState_eq","acTapes","and_self","and_true","bitCodec_encodeEntry","buildComp_succ_of_query","buildComp_zero_of_ret","decide_eq_false","decide_eq_true","decide_eq_true_eq","hCnt","hEnc","hFwd","hI","hIst","hL","hLat","hNew","hS","hU","hW","hX","hZ","hc'","hlen","hlog","hs'","h₁","h₂","h₃","if_neg","if_pos","length_pairEncode","msgOf_eq","ofFn_acSeedTapes","ofFn_padFin_of_length","ofFn_zeroBits","pairFstD_pairEncode","pairSndD_pairEncode","rEnc","rFwd","rIst","rLat","rMsg","rNew","rTape","seedIn_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler

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

end TCSlib.Cryptography.Composability.AdaptiveCPA
