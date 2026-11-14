/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Signature forger codecs read through their published fields

## Main definitions

This module introduces no definitions.

## Main results

* `Games.MachineCodec.ext_of_fields`: codecs with equal decoding, entry encoding,
  and timeout fields are equal.
* `Authentication.SignatureScheme.forgerCodec_eq_bitCodec`: the signature
  forger codec equals the canonical bit codec at its declared lengths.
* `HashSignFill.splitBits_append`, `splitBits_pad_concat`: splitting fixed-width
  concatenated words recovers their components, including zero widths.

The generic extensionality lemma is a promotion request for `Games/Machines`;
the signature-specific reader belongs beside its definition in `Signatures/Defs`.
The two split-word readers are promotion requests for `Authentication/Encoding`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 144.1 (technical support for its machine reductions).
-/

namespace TCSlib.Cryptography.Games.MachineCodec

/-- Two machine codecs are equal when their move decoders, entry encoders and timeout
outputs are equal. These are all three fields of `MachineCodec`.

**Proof sketch.** Destructure the two records. Substituting the three field equalities
leaves the same constructor on both sides. -/
theorem ext_of_fields {ι α : Type} {spec : OracleSpec ι}
    (a b : MachineCodec spec α)
    (hdecode : a.decodeMove = b.decodeMove)
    (hentry : a.encodeEntry = b.encodeEntry)
    (htimeout : a.timeout = b.timeout) : a = b := by
  cases a
  cases b
  cases hdecode
  cases hentry
  cases htimeout
  rfl

end TCSlib.Cryptography.Games.MachineCodec

namespace TCSlib.Cryptography.Authentication.SignatureScheme

open TCSlib.Cryptography.Games

/-- The signature forger codec is the bit codec with message-length queries,
signature-length answers and a message-plus-signature-length final output.

**Proof sketch.** The published decoding, entry-encoding and timeout equations agree
with those of the bit codec. Codec extensionality turns those field equations into
equality of the complete records; neither codec's definition is unfolded. -/
theorem forgerCodec_eq_bitCodec (S : SignatureScheme) (n : ℕ) :
    S.forgerCodec n =
      bitCodec (fun _ : Fin 1 => S.msgLen.eval n) (fun _ : Fin 1 => S.sigLen.eval n)
        (S.msgLen.eval n + S.sigLen.eval n) := by
  apply MachineCodec.ext_of_fields
  · funext w
    exact (S.forgerCodec_decodeMove n w).trans
      (bitCodec_decodeMove (fun _ : Fin 1 => S.msgLen.eval n)
        (fun _ : Fin 1 => S.sigLen.eval n) (S.msgLen.eval n + S.sigLen.eval n) w).symm
  · funext e
    exact (S.forgerCodec_encodeEntry n e).trans
      (bitCodec_encodeEntry (fun _ : Fin 1 => S.msgLen.eval n)
        (fun _ : Fin 1 => S.sigLen.eval n) (S.msgLen.eval n + S.sigLen.eval n) e).symm
  · exact (S.forgerCodec_timeout n).trans
      (bitCodec_timeout (fun _ : Fin 1 => S.msgLen.eval n)
        (fun _ : Fin 1 => S.sigLen.eval n) (S.msgLen.eval n + S.sigLen.eval n)).symm

end TCSlib.Cryptography.Authentication.SignatureScheme

namespace TCSlib.Cryptography.Authentication.HashSignFill

/-- Splitting the concatenation of two fixed-width words recovers the two words. -/
theorem splitBits_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    splitBits (Fin.append x y) = (x, y) := by
  apply Prod.ext
  · funext j
    rw [splitBits_fst, Fin.append_left]
  · funext j
    rw [splitBits_snd, Fin.append_right]

/-- Reading the concatenated encodings of two words at their total width and splitting the
result recovers the original words. This also covers zero widths. -/
theorem splitBits_pad_concat {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    splitBits (padFin (a + b) (List.ofFn x ++ List.ofFn y)) = (x, y) := by
  rw [← List.ofFn_fin_append, padFin_ofFn, splitBits_append]

end TCSlib.Cryptography.Authentication.HashSignFill
