import TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction
open Lean Elab Command

namespace TCSlib.Cryptography.Authentication.PRFMAC
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
open TCSlib.Cryptography.Composability.ChallengeSim (expect_sample_prod)

def idsToCheck : List String := ["Bool.decide_and","Composability.PRFGame.ofFn_evalFn_toCompOn","Fin.append_castAdd_natAdd","List.drop_left'","List.headD_cons","List.length_append","List.length_map","List.length_nil","List.length_reverse","List.length_singleton","List.map_append","List.map_singleton","List.mem_map","List.mem_reverse","List.ofFn_fin_append","List.reverse_append","List.reverse_singleton","List.singleton_append","List.take_left'","Nat.zero_add","OracleComp.allOutputs_pure","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","QueryImpl.comp_apply","QueryImpl.ofComp_apply","QueryImpl.withLog_apply","decide_fnForge","expect_bind","expect_congr_of_allOutputs","expect_pure","expect_sample_comm","expect_sample_equiv","expect_sample_prod","expect_toCompOn_outLen","fnForge_iff","fnImpl_apply","fnImpl_eq","h2","hQ","hd","hdrop","headD_ofFn_one","hinit","hm","hout","hrun","htake","hw","hφ₀","hφ₄","key","length_queried","macBudget","macBudget_eval","macHandler_finCall","macHandler_finish","macHandler_impl","macHandler_init_eq","macHandler_outLen","macHandler_perCall","ofFn_padFin_of_length","padFin_ofFn","queried_append","queried_eq","queried_nil","show","simulate_bind","simulate_comp","simulate_eq_of_abs_bounded","simulate_pure","simulate_query"]
def scannedModule : Name := `TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction

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

end TCSlib.Cryptography.Authentication.PRFMAC
