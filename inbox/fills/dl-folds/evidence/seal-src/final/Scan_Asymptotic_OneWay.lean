import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.OneWayYao
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.OneWayFunctions.Amplification
import Mathlib.Logic.Equiv.Fin.Basic

open Lean Elab Command Meta

/-! Seal census of the dl-folds fill (final) for `TCSlib/Cryptography/Asymptotic/OneWay.lean`: the module's own imports, and every seal
candidate of its full TCSlib import closure (semireducible, non-instance, non-projection,
non-private TCSlib definitions; all are foreign to the file). One `CAND` line each. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  let mut skipped : Nat := 0
  for (c, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.toString.startsWith "TCSlib" do continue
    unless ci matches .defnInfo _ do continue
    if c.isInternal || isPrivateName c then skipped := skipped + 1; continue
    if isInstanceCore env c || env.isProjectionFn c || isAuxRecursor env c ||
        isNoConfusion env c then skipped := skipped + 1; continue
    if getReducibilityStatusCore env c != .semireducible then skipped := skipped + 1; continue
    out := out.push s!"CAND {c.toString (escape := true)} | {mod}"
  for s in out.qsort (· < ·) do IO.println s
  IO.println s!"TOTAL {out.size} candidates; {skipped} TCSlib definitions skipped"
