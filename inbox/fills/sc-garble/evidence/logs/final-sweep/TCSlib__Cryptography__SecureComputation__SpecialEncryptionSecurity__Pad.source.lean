/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-prefix and slice masks of special encryption

## Main definitions

* `SecureComputation.sliceMask`: the zero/message/zero full-width mask for a fitting slice.

## Main results

* `SecureComputation.spEncStr_eq_zeroPrefixMask`: the full ciphertext body is the XOR of
  a zero-prefix message with the pad.
* `SecureComputation.spEncStr_eq_sliceMask`: cutting a full masked pad gives a slice ciphertext.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Algorithm 157.2.
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-- Special encryption masks the zero-prefix message:
`spEncStr E k m r = ⟨r, (0^{|r|} ++ m) ⊕ E(⟨k,r⟩)⟩`, whenever the pad has at least
`|r| + |m|` bits. [PS10, §6.2.2, Algorithm 157.2]

**Proof sketch.** Split the pad after the nonce length. Split XOR at the same boundary;
its prefix is unchanged by the zero mask, and its suffix is the encrypted message.
The pad-length hypothesis makes the prefix exactly as long as the nonce. -/
theorem spEncStr_eq_zeroPrefixMask (E : List Bool → List Bool) (k m r : List Bool)
    (hp : r.length + m.length ≤ (E (pairEncode k r)).length) :
    spEncStr E k m r = pairEncode r
      (List.zipWith xor (List.replicate r.length false ++ m) (E (pairEncode k r))) := by
  rw [spEncStr_eq]
  congr 1
  have hlen : ((E (pairEncode k r)).take r.length).length = r.length := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  conv_rhs => rw [← List.take_append_drop r.length (E (pairEncode k r))]
  rw [List.zipWith_append (by rw [List.length_replicate, hlen])]
  congr 1
  rw [List.zipWith_comm_of_comm Bool.xor_comm]
  simpa only [hlen] using
    (MultiMsg.zipWith_xor_replicate_false ((E (pairEncode k r)).take r.length)).symm

/-- A full-width slice mask, padded with zeros:
`sliceMask L n o m = padFin L (0^{o+n} ++ m ++ 0^{L-(o+n+|m|)})`.
[PS10, Theorem 99.2 with slices] -/
def sliceMask (L n o : ℕ) (m : List Bool) : Fin L → Bool :=
  padFin L (List.replicate (o + n) false ++ m ++
    List.replicate (L - (o + n + m.length)) false)

/-- `sliceMask L n o m = padFin L (0^{o+n} ++ m ++ 0^{L-(o+n+|m|)})`. -/
theorem sliceMask_eq (L n o : ℕ) (m : List Bool) :
    sliceMask L n o m = padFin L (List.replicate (o + n) false ++ m ++
      List.replicate (L - (o + n + m.length)) false) := rfl

/-- A fitting slice mask has its specified full-width word:
`⟦sliceMask L n o m⟧ = 0^{o+n} ++ m ++ 0^{L-(o+n+|m|)}` if `o+n+|m| ≤ L`. -/
theorem ofFn_sliceMask (L n o : ℕ) (m : List Bool) (h : o + n + m.length ≤ L) :
    List.ofFn (sliceMask L n o m) = List.replicate (o + n) false ++ m ++
      List.replicate (L - (o + n + m.length)) false := by
  rw [sliceMask_eq]
  apply ofFn_padFin_of_length
  simp only [List.length_append, List.length_replicate]
  omega

/-- Cutting a masked full-width pad gives special encryption from that slice:
`spEncStr (fun _ => pad.drop o) k m r =
  ⟨r, ((⟦sliceMask L |r| o m⟧ ⊕ pad).drop o).take (|r|+|m|)⟩`,
if `|pad|=L` and `o+|r|+|m| ≤ L`. [PS10, §6.2.2, Algorithm 157.2, with slices]

**Proof sketch.** The fitting mask has the exact zero/message/zero word. Drop the leading
offset and take the nonce/message width using the existing zip-with window identities.
The selected mask is precisely `0^{|r|} ++ m`. The zero-prefix special-encryption identity
then gives the ciphertext; zip-with truncation discards the unused remainder of the pad. -/
theorem spEncStr_eq_sliceMask (L o : ℕ) (pad k m r : List Bool)
    (hp : pad.length = L) (hfit : o + r.length + m.length ≤ L) :
    spEncStr (fun _ => pad.drop o) k m r = pairEncode r
      (((List.zipWith xor (List.ofFn (sliceMask L r.length o m)) pad).drop o).take
        (r.length + m.length)) := by
  have hdrop : r.length + m.length ≤ (pad.drop o).length := by
    rw [List.length_drop, hp]
    omega
  rw [spEncStr_eq_zeroPrefixMask _ _ _ _ hdrop, ofFn_sliceMask _ _ _ _ hfit]
  congr 1
  rw [List.drop_zipWith, List.take_zipWith]
  have hmask : ((List.replicate (o + r.length) false ++ m ++
      List.replicate (L - (o + r.length + m.length)) false).drop o).take
        (r.length + m.length) = List.replicate r.length false ++ m := by
    rw [List.append_assoc, List.drop_append_of_le_length (by simp),
      List.drop_replicate]
    have ho : o + r.length - o = r.length := by omega
    rw [ho, ← List.append_assoc]
    have hl : (List.replicate r.length false ++ m).length = r.length + m.length := by
      rw [List.length_append, List.length_replicate]
    rw [← hl, List.take_left]
  rw [hmask]
  have ht := List.zipWith_eq_zipWith_take_min
    (f := xor) (l₁ := List.replicate r.length false ++ m) (l₂ := pad.drop o)
  have hlen : (List.replicate r.length false ++ m).length = r.length + m.length := by
    rw [List.length_append, List.length_replicate]
  simpa only [hlen, Nat.min_eq_left hdrop, List.take_of_length_le hlen.le] using ht

end TCSlib.Cryptography.SecureComputation
