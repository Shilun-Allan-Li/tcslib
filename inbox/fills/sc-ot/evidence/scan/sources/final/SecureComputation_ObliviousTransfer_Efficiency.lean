import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Efficiency
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.OT
open Complexity Turing TCSlib.Cryptography

def idsToCheck : List String := ["List.cons_append","List.headD_cons","List.length_drop","List.length_ofFn","List.length_replicate","List.length_singleton","List.length_take","List.length_zipWith","List.mem_cons","List.nil_append","List.not_mem_nil","List.ofFn_congr","List.ofFn_get","NUPPT.Uniform.advice_eq","NUPPT.advInput_eq","NUPPT.inArg_layout","NUPPT.inCoins_layout","NUPPT.inParam_layout","NUPPT.layout_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_normal","PolyExpr.eval_subst","Protocol.transcript_eq_transcriptWith","Strategy.coinLen_eq","Strategy.encodeMsgs_cons","Strategy.encodeMsgs_nil","Strategy.ofNUPPT_next","advInput_layout","genRaw_eq","genRaw_layout","getD_one_eq","getD_one_eq'","getD_zero_eq","hP","hPc","hQ₃","hV","hVc","headD_eq_pairFstD","hout","hpair","hrB","if_neg","if_pos","knownRaw_eq","knownRaw_layout","length_pairEncode","maskRaw_eq","maskRaw_layout","mask_eq","or_false","outRaw_eq","pairEncode_ne_nil","pairFstD_nil","pairFstD_pairEncode","pairRaw_eq","pairSndD_nil'","pairSndD_pairEncode","rawRaw_eq","rawRaw_layout","receiverNext_eq","receiverNext_pair","receiverNext_single","receiverRaw_advInput","receiverRaw_eq","runAtL_eq_layout","senderNext_eq","senderNext_nil","senderNext_single","senderRaw_advInput","senderRaw_eq","transcriptWith_isOT"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Efficiency

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

end TCSlib.Cryptography.SecureComputation.OT
