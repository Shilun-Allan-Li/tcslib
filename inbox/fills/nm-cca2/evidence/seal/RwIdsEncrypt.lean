import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
open Lean Elab Command

/-! Explicit readings of the nm-cca2 fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Encrypt.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.NMCCA2
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open AdaptiveCPA (acDin acDout acDout_zero)

def idsToCheck : List String := ["EnsembleLemmas.length_padL","Fin.cons_zero","FixedLengthScheme.decAnswer_some","Function.comp_apply","InteractiveHandler.advInput_eq","InteractiveHandler.finish_eq","List.length_append","List.length_drop","List.length_ofFn","List.length_replicate","List.length_take","List.ofFn_const","List.ofFn_succ","List.replicate_succ","List.replicate_succ'","NUPPT.Uniform.runAt_eq","NUPPT.advInput_eq","NUPPT.coinsEquivPoly_symm_ofFn","NUPPT.distinguisherL_eq","NUPPT.runAt_eq","PolyExpr.eval_add","PolyExpr.eval_const","S.indImpl_challenge_none_onSpec","S.indImpl_challenge_repeat_onSpec","S.indImpl_dec_onSpec","eBit","eCt","eFin","eMsg","eTape","encCt_eq","encHandler","encHandler_finCall","encHandler_outLen","encHandler_seedLen","encTape_eq","fwdHandler_advIn","fwdHandler_finCall","fwdHandler_finRun","fwdHandler_outLen","fwdHandler_perCall","fwdHandler_seedLen","guessBit_eq","guessFun","h","h0","h2","hA","hCt","hU","hW","hZ","hfin","hm","hrun","hω","if_neg","if_pos","ofFn_encTape","ofFn_zeroBits","pairFstD_pairEncode","pairSndD_pairEncode","seedIn_eq"]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let s' := if s.startsWith "S." then "FixedLengthPKScheme." ++ (s.drop 2) else s
    let n := s'.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> pure []
    let env ← getEnv
    let modOf (c : Name) : String :=
      ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!.toString).getD "?"
    if cands.isEmpty then IO.println s!"{s}: (unresolved: local hypothesis or private)"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some _ => "other"
        | none => "?"
      IO.println s!"{s}: {c}: {k} ({modOf c})"

end TCSlib.Cryptography.Composability.NMCCA2
