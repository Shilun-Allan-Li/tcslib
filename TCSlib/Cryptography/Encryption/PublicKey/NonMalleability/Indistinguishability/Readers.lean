/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Requested readers of the public-key decryption oracle

**Reader request (escalation of the `nm-cca2` fill).** The published decryption equation
`FixedLengthPKScheme.indImpl_dec_onSpec` (`PublicKey/OracleSecurity.lean`) states the valid answer
`decAnswer (…) : Fin (msgLen(n) + 1) → Bool` at the oracle's answer type `(S.indSpec n).rng 0`
without a cast: the two types agree only by unfolding `outLens`. A consumer that reads the answer
as a string (the CCA2 reduction of [PS10, Theorem 175.9] compares it with the non-malleability
experiment's decryption) must therefore identify `Fin (S.outLens n 0)` with
`Fin (S.msgLen.eval n + 1)` by unfolding, which Rule 10 forbids outside `OracleSecurity.lean`. The
private-key file publishes the cast form (`FixedLengthScheme.indSpec_decRng` and its
`indImpl_dec_onSpec`); the public-key file does not.

This module states the two missing readers in the form requested for
`PublicKey/OracleSecurity.lean`. The first is proved from published readers. The second is the
**only** declaration of the fill that reads a foreign definition (`outLens`) definitionally: its
proof is the one-line proof it would have in its home file. At landing both move to
`OracleSecurity.lean` (as `FixedLengthPKScheme.indSpec_decRng` and a cast form of
`indImpl_dec_onSpec`) and this module is deleted.

## Main results

* `NMCCA2.indSpec_decRng`: the decryption oracle's answer type.
* `NMCCA2.indImpl_dec_onSpec_cast`: the decryption equation with the answer cast.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 171.5 (book p. 171).
-/

namespace TCSlib.Cryptography.Composability.NMCCA2

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable (S : FixedLengthPKScheme)

/-- **Requested reader.** The decryption oracle answers a validity flag and a message:
`(S.indSpec n).rng 0 = (Fin (msgLen(n) + 1) → Bool)`. -/
theorem indSpec_decRng (n : ℕ) : (S.indSpec n).rng 0 = (Fin (S.msgLen.eval n + 1) → Bool) := by
  rw [S.indSpec_rng, S.outLens_zero]

/-- **Requested reader** (the cast form of `FixedLengthPKScheme.indImpl_dec_onSpec`). A decryption
query `c` (read through the width equality) in state `s` checks the oracle's availability and
refuses the recorded challenge; otherwise it answers `Dec_sk(c)` encoded by `decAnswer`, read at
the oracle's answer type through `indSpec_decRng`:
`S.indImpl atk b n pk sk 0 c s = if decOpen atk s.isSome && s ≠ some c then
pure (cast _ (decAnswer (decodeFin _ (Dec ⟨sk, c⟩))), s) else pure (0, s)`.

**Rule 10 exception (disclosed):** the proof reads `outLens` definitionally through `cast_eq`, as
it would in `OracleSecurity.lean`, where it belongs. -/
theorem indImpl_dec_onSpec_cast (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : (S.indSpec n).dom 0) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
      then .pure (cast (indSpec_decRng S n).symm (FixedLengthScheme.decAnswer
        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c)))))), s)
      else .pure (zeroBits _, s) := by
  simpa only [cast_eq] using S.indImpl_dec_onSpec atk b n pk sk c s

end TCSlib.Cryptography.Composability.NMCCA2
