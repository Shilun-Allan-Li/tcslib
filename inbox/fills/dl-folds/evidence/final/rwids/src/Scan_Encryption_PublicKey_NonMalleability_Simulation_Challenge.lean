import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Challenge
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
open TCSlib.Cryptography.Games.InteractiveHandler (rU_input rS_input rI_input rX_input rL_input polyTimeComputable_rU polyTimeComputable_rS polyTimeComputable_rI polyTimeComputable_rX polyTimeComputable_rL)

def idsToCheck : List String := ["EnsembleLemmas.padL_eq","Function.comp_apply","Games.padFin_replicate_false","InteractiveHandler.impl_of_query_padFin","InteractiveHandler.impl_of_ret_padFin","List.drop_one","List.headD_cons","List.length_append","List.length_cons","List.length_ofFn","List.length_replicate","List.replicate_succ","List.tail_cons","Nat.add_assoc","Nat.add_comm","Option.isSome_none","Option.isSome_some","P.ansH_len","P.ansY_len","P.qry_len","PolyExpr.eval_add","PolyExpr.eval_const","chalHandler_impl_dec","chalHandler_impl_none","chalHandler_impl_some","chalHandler_perCall","chalHandler_stateLen","chalHandler_stateLen_eval","chalRun_eq","chalState_none","chalState_some","hH","hI","hI₀","hI₁","hL₀","hL₁","hQ₁","hS","hS₀","hS₁","hU","hU₀","hU₁","hW₁","hY","hans","headD_ofFn_chalState","hq","hx","if_neg","ofFn_chalState_none","ofFn_chalState_some","ofFn_padFin_of_length","ofFn_zeroBits","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","rU_input","snmDin_one","snmDout_one","snmDout_zero"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Challenge

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

end TCSlib.Cryptography.Composability.NMSim
