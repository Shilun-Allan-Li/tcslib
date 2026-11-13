import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.IndSim
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.EnsembleLemmas (seedEquiv seedEquivPoly ofFn_padFin_eq_padL)

def idsToCheck : List String := ["Bool.true_and","ChallengeSim.expect_sample_prod","EnsembleLemmas.length_padL","Games.simulate_eq_of_abs","List.append_assoc","List.drop_left'","List.drop_one","List.drop_replicate","List.drop_succ_cons","List.headD_cons","List.length_append","List.length_ofFn","List.tail_cons","List.take_left'","Nat.add_comm","Option.getD_none","Option.getD_some","Option.map_none","Option.map_some","Option.some.injEq","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","ProbComp.expect_bind","ProbComp.expect_pure","ProbComp.expect_sample_equiv","accept_nmGame_eq_rImpl","chalHandler_init","chalHandler_stateLen_eval","decide_eq_decide","drawWith_eq","finMsg_eq","hB","hK","headD_ofFn_chalState","hfin","hs","hybAcc_eq","hφ","hω","length_ofFn_coins","nmAbs_none","nmAbs_snd_fst","nmAbs_some","nmParams_advInput","nmParams_outLen_eval","nmSeed_eq","ofFn_chalState_none","ofFn_chalState_some","ofFn_padFin_eq_padL","ofFn_padFin_of_length","ofFn_zeroBits","pairSndD_pairEncode","realView_eq","recDist_distinguisherL","recView_nmOut","recView_nmOutL","samp.runAtL_eq_output_layout","samp.runAt_eq","simulate_bind","simulate_comp","simulate_pure","stParam_eq","stParam_nmAbs"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.IndSim

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
