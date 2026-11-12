import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.AdaptiveCPA
open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

def idsToCheck : List String := ["Function.update_eq_self","Function.update_idem","Function.update_of_ne","Function.update_self","List.length_cons","OracleComp.bind_assoc","OracleComp.pure_bind","castImpl_eq","castImpl_self","dif_neg","dif_pos","expect_bind","expect_pure","expect_sample_comm","expect_sample_prod","extTape","extTape_of_lt","h","hF","hT","he","hj","hl","hsel","hybImpl","hybImpl_fresh","hybImpl_full","hybImpl_zero","if_neg","if_pos","padFin_ofFn","simulate_pure","simulate_query","tapeImpl","tapeImpl_eager","tapeImpl_full","tapeImpl_lazy","tapeImpl_zero"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid

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
