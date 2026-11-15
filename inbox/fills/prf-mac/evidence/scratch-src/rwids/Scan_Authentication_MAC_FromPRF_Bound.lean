import TCSlib.Cryptography.Authentication.MAC.FromPRF.Bound
open Lean Elab Command

namespace TCSlib.Cryptography.Authentication.PRFMAC
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["Bridge.acceptGame_eq","Bridge.acceptProb_eq","List.length_ofFn","accept_eq","accept_forgeGame_eq","distAdv_def","eval_toOracleAdversary_width₂","expect_const","expect_sample_comm","expect_sample_equiv","h","hD","hacc","hadv","he","hreal","ht","htag","inv_pow","ofFn_padFin_of_length","oracleDist_apply","padFin_ofFn","prfAdv_def","prob_bind","prob_pure","randomFunction_apply"]
def scannedModule : Name := `TCSlib.Cryptography.Authentication.MAC.FromPRF.Bound

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
