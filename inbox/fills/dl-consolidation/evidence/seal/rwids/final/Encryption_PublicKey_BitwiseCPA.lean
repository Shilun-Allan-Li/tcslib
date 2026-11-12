import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA
open Lean Elab Command

namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open ChallengeSim BitwiseSim ProbComp

def idsToCheck : List String := ["BitPublicKeyScheme.bitwiseEncCoins_ofFn","BitPublicKeyScheme.bitwise_enc","BitPublicKeyScheme.bitwise_enc_runAtL","BitPublicKeyScheme.bitwise_gen","BitPublicKeyScheme.pkEncDist_eq","Bool.false_eq_true","Bridge.acceptGame_eq","Bridge.acceptProb_eq","Equiv.trans_apply","FixedLengthPKScheme.INDSecure_iff","FixedLengthPKScheme.inLens_one","FixedLengthPKScheme.inLens_zero","FixedLengthPKScheme.indCodec_eq_bitCodec","FixedLengthPKScheme.indGame_eq","FixedLengthPKScheme.outLens_one","FixedLengthPKScheme.outLens_zero","FixedLengthScheme.ofFn_splitHalf_fst","FixedLengthScheme.ofFn_splitHalf_snd","Function.update_of_ne","Function.update_self","List.getD_eq_getElem?_getD","List.getElem?_eq_getElem","List.getElem_append","List.getElem_ofFn","List.headD_cons","List.length_ofFn","List.length_replicate","List.ofFn_succ","List.ofFn_zero","NUPPT.coinLen_eq","NUPPT.coinsCongr_ofFn","NUPPT.distinguisherL_eq","NUPPT.runAt_eq","Nat.cast_zero","Option.elim_none","Option.elim_some","Option.getD_some","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","PublicKeyScheme.padded_ctLen","PublicKeyScheme.padded_enc_runAt","PublicKeyScheme.padded_msgLen","abs_zero","accept_eq","accept_indGame_eq","advantage_eq","bitwise_runAt_blocks","bwAux","bwLaux","chRun_congr","coinBlock_ofFn_coinBlocks","dif_pos","distAdv_def","div_le_iff₀","expect_sample_comm","expect_sample_equiv","expect_sample_prod","expect_sample_update","expect_sub","h","h'","hD","hH","ha","hans","hgen","hl","hmm","hpt","hrun","hseed","hybCt","hybGame","hyb_advantage_eq","hz","hφ","h₀","h₁","h₂","h₃","i.isLt","if_false","if_neg","if_pos","if_true","length_of_firstQ_eq_some","length_pairEncode","ofFn_cast","ofFn_getD_split","ofFn_half","pairFstD_pairEncode","plantAns_eq","plantOut_init","plantOut_recorded","plantTuple_spec","planted_eq","prob_bind","prob_pure","qDin_one","qDin_zero","qDout_one","qDout_zero","reduceIte","seedIn_eq","sub_self","zero_mul"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA

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

end TCSlib.Cryptography.Composability
