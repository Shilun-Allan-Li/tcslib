import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Readers
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Decrypt
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Encrypt

open Lean Elab Command Meta

/-! Seal census of the nm-cca2 fill for `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean`: the module's own imports, and every seal candidate
of its full TCSlib import closure (semireducible (neither reducible nor already irreducible), non-instance, non-projection, non-private
TCSlib definitions; all are foreign to the file). One `CAND` line each. -/

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
