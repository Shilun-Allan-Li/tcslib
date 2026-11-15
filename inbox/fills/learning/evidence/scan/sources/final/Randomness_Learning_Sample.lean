import TCSlib.Cryptography.Randomness.Learning.Sample
open Lean Elab Command

namespace TCSlib.Cryptography.Randomness.LearnPRF
open Complexity Turing TCSlib.Cryptography

def idsToCheck : List String := ["Function.comp_apply","GGMRed.pairEncode_append_right","List.concat_eq_append","List.drop_left'","List.flatMap_cons","List.flatten_append","List.flatten_singleton","List.foldr_cons","List.length_nil","List.length_ofFn","List.length_replicate","List.nil_append","List.ofFn_succ'","List.take_left'","MultiMsg.eval_histBlockLen","MultiMsg.flatMap_ofFn","MultiMsg.flatMap_range_blocks","MultiMsg.length_flatten_of_length","PolyExpr.eval_mul","blk","firstBit_eq","foldr_pairEncode_nil","hflat","hsplit","ih","lastLabel_eq","lastPair_eq","learnIn_eq","length_pairEncode","pairFstD_pairEncode","pairSndD_pairEncode","relabel_eq","sampleLen","sampleLen_eval","sampleOf_eq","tupleWord_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Randomness.Learning.Sample

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

end TCSlib.Cryptography.Randomness.LearnPRF
