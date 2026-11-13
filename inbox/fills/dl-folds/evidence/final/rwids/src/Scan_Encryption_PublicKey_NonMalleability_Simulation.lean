import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open NMSim
open TCSlib.Cryptography.Composability.MsgSampler
open TCSlib.Cryptography.Composability.FixedLengthPKScheme

def idsToCheck : List String := ["Fin.cons_succ","Fin.cons_zero","FixedLengthScheme.decOpen_cpa","Games.castImpl_eq","Games.padFin_ofFn_zeroBits","List.headD_cons","List.length_ofFn","List.ofFn_fin_append","List.ofFn_succ","List.tail_cons","M.draw_eq","M.histAt_eq","NMSim.hybAcc_true_eq_false","NMSim.realAcc_eq_hybAcc","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","ProbComp.prob_bind","ProbComp.prob_pure","S.NMSecure_iff","S.snmImpl_challenge","S.snmImpl_dec","abs_mul","abs_neg","abs_two","abs_zero","accept_eq","accept_snmIdeal_eq","accept_snmReal_eq","advantage_eq","castImpl_snmImpl","decide_map_ofFn","drawWith_eq","encWith_eq","entryL_eq","hB","hSim","hab","hc","histImpl_eq","histWith_eq","hx","idealAcc_eq","idealView_eq","if_neg","if_pos","ofFn_block_eq_coinBlock","ofFn_natAdd_eq_drop","ofFn_snmEntry","ofFn_zeroBits","rImpl_dec","rImpl_none_eager","rImpl_none_lazy","rImpl_some","realAcc_eq","realView_eq","simEntry_fst","simImpl_eq","simImpl_eq_histImpl","snmCt_eq","snmDin_one","snmDin_zero","snmDout_one","snmDout_zero","snmEntry_eq","snmIdeal_eq","snmImpl","snmInLens_one","snmInLens_zero","snmOutLens_one","snmOutLens_zero","snmReal_eq","snmSigma_eq","snmView_eq","snmView_idealView","snmView_realView","sub_self"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation

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

end TCSlib.Cryptography.Composability
