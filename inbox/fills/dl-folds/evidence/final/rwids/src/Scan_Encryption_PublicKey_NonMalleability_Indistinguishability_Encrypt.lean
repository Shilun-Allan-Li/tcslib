import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Encrypt
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.NMCCA2
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
open TCSlib.Cryptography.Games.InteractiveHandler (rU_finInput rZ_finInput rW_finInput finA_finInput polyTimeComputable_rU polyTimeComputable_rZ polyTimeComputable_rW polyTimeComputable_finA)
open AdaptiveCPA (acDin acDout acDout_zero)

def idsToCheck : List String := ["EnsembleLemmas.length_padL","Fin.cons_zero","FixedLengthScheme.decAnswer_some","Function.comp_apply","InteractiveHandler.advInput_eq","InteractiveHandler.finish_eq","List.length_append","List.length_drop","List.length_ofFn","List.length_replicate","List.length_take","List.ofFn_const","List.ofFn_succ","List.replicate_succ","List.replicate_succ'","NUPPT.Uniform.runAt_eq","NUPPT.advInput_eq","NUPPT.coinsEquivPoly_symm_ofFn","NUPPT.distinguisherL_eq","NUPPT.runAt_eq","PolyExpr.eval_add","PolyExpr.eval_const","eBit","eCt","eFin","eMsg","eTape","encCt_eq","encHandler","encHandler_finCall","encHandler_outLen","encHandler_seedLen","encTape_eq","fwdHandler_advIn","fwdHandler_finCall","fwdHandler_finRun","fwdHandler_outLen","fwdHandler_perCall","fwdHandler_seedLen","guessBit_eq","guessFun","h2","hA","hCt","hU","hW","hZ","hfin","hm","hrun","hω","if_neg","if_pos","ofFn_encTape","ofFn_zeroBits","pairFstD_pairEncode","pairSndD_pairEncode","seedIn_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Encrypt

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

end TCSlib.Cryptography.Composability.NMCCA2
