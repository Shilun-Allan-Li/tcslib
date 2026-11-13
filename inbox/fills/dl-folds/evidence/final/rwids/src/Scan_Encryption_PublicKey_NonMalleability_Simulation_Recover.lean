import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Recover
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open NMCCA2 (guessBit guessBit_eq guessBit_valid guessBit_refused polyTimeComputable_guessBit)

def idsToCheck : List String := ["Bool.false_eq_true","EnsembleLemmas.padL_eq","Function.comp_apply","List.append_assoc","List.append_nil","List.drop_left'","List.drop_one","List.eq_replicate_iff","List.flatten_append","List.flatten_cons","List.flatten_flatten","List.flatten_nil","List.length_append","List.length_drop","List.length_flatten","List.length_map","List.length_range","List.length_replicate","List.map_append","List.map_congr_left","List.map_cons","List.map_const'","List.map_flatten","List.map_map","List.map_nil","List.mem_cons","List.mem_range","List.not_mem_nil","List.ofFn_const","List.sum_replicate","List.tail_cons","List.take_left'","NUPPT.Uniform.runAt_eq","NUPPT.advInput_eq","NUPPT.coins_ofPolyTime","NUPPT.distinguisherL_eq","NUPPT.inAdvice_layout","NUPPT.inArg_layout","NUPPT.inCoins_layout","NUPPT.inParam_layout","NUPPT.layout_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAtL_ofPolyTime","NUPPT.runAt_coinsCongr","NUPPT.runAt_eq","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","bitG_eq","chunkMap_flatten","ctxSt_eq","decide_false","encBit_eq","encF_eq","encPair_eq","entF_eq","entryL_drop_one","entryL_eq","h","h1","h2","h3","hB","hE","hP","hW","ha","haP","hbits","hc","hcs","hctx","hdec","henc","heq","hf","hfdef","hfl","hg","hlay","hmP","hv","hvdef","hz","hω","hℓ","if_neg","if_pos","ih","length_entryL","length_flatten_map_range","map_coinBlock_flatten","nmLen_eval","nmOutL_eq","nmOutput_eq_entryTails","nmOutput_flatten","ofFn_zeroBits","or_false","pairFstD_pairEncode","pairSndD_pairEncode","recDist","recFun","recView_eq","reduceIte","smul_eq_mul","this"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Recover

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
