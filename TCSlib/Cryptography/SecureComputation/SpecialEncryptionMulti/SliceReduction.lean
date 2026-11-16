/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti.SliceParser
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.Pad

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Slice advice and the D4 consumer

## Main definitions

* `SliceReduction.sliceAdvice`: unary offsets and window widths in the list encoding.

## Main results

* `SliceReduction.exists_slicePost_nuppt`: hard-wire polynomial-length slice advice.
* `SliceReduction.slicePost_tuple`: the same-seed identity with special slice ciphertexts.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, Theorem 99.2 with slices.
-/

namespace TCSlib.Cryptography.SecureComputation.SliceReduction

open Complexity Turing TCSlib.Cryptography

/-- Hard-wiring polynomial-length advice after the slice parser gives a PPT reduction:
`∃ B, ∀ n, ∃ e : D.Coins n ≃ B.Coins n, ∀ y r,
  B.distinguisherL n y (e r) = D.distinguisherL n (slicePost ⟨β n,y⟩) r`,
provided `|β n| ≤ b(n)`. [PS10, Theorem 99.2, with slices]

**Proof sketch.** Precompose `D` with the total polynomial-time slice parser, swapping the
argument/advice pair into the parser's order. Hard-wire the extra advice with the published
NUPPT closure theorem. Both operations preserve the coin polynomial; its canonical coin
congruence preserves the raw coin string, so the activation and verdict equations hold
pointwise, on arbitrary parser inputs. -/
theorem exists_slicePost_nuppt (D : NUPPT) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, ∀ n, ∃ e : D.Coins n ≃ B.Coins n, ∀ y r,
      B.distinguisherL n y (e r) =
        D.distinguisherL n (slicePost (pairEncode (β n) y)) r := by
  obtain ⟨A, hAc, -, -, hA⟩ := D.exists_comp
    (polyTimeComputable_slicePost.comp'
      (polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD))
    polyTimeComputable_id
  obtain ⟨B, hBc, hB⟩ := A.exists_withAdvice β b hβ
  have hc : D.coins = B.coins := (hBc.trans hAc).symm
  refine ⟨B, fun n => ⟨NUPPT.coinsCongr hc n, fun y r => ?_⟩⟩
  rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq,
    NUPPT.runAt_coinsCongr hc, hB, hA, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [NUPPT.runAt_eq]
  rfl

/-- The slice descriptor advice is the encoded list of unary offset/width pairs:
`sliceAdvice n o len = encodeList (List.ofFn fun i => ⟨1^{o i},1^{n+len i}⟩)`. -/
def sliceAdvice {Q : ℕ} (n : ℕ) (o len : Fin Q → ℕ) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun i =>
    pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true))

/-- `sliceAdvice n o len = encodeList (List.ofFn fun i => ⟨1^{o i},1^{n+len i}⟩)`. -/
theorem sliceAdvice_eq {Q : ℕ} (n : ℕ) (o len : Fin Q → ℕ) :
    sliceAdvice n o len = PrivateKeyScheme.encodeList (List.ofFn fun i =>
      pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true)) := rfl

/-- Uniformly bounded entries have a linearly bounded list encoding:
`(∀ c ∈ l, c.length ≤ B) → (encodeList l).length ≤ l.length*(2*B+2)`. -/
theorem length_encodeList_le (l : List (List Bool)) (B : ℕ)
    (h : ∀ c ∈ l, c.length ≤ B) :
    (PrivateKeyScheme.encodeList l).length ≤ l.length * (2 * B + 2) := by
  induction l with
  | nil =>
    simp only [PrivateKeyScheme.encodeList_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons c l ih =>
    have hc := h c (List.mem_cons_self)
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    rw [PrivateKeyScheme.encodeList_cons, length_pairEncode, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

/-- Fitting slice advice has polynomial length:
`o i+n+len i ≤ L → |sliceAdvice n o len| ≤ Q*(6*L+6)`.
This includes empty messages and slices that fit exactly.

**Proof sketch.** Each descriptor has at most `3*L+2` bits by the fit inequality. Each
encoded-list entry adds twice that length plus two delimiters. Apply the general list
encoding length bound to its `Q` entries. -/
theorem length_sliceAdvice_le {Q : ℕ} (L n : ℕ) (o len : Fin Q → ℕ)
    (hfit : ∀ i, o i + n + len i ≤ L) :
    (sliceAdvice n o len).length ≤ Q * (6 * L + 6) := by
  rw [sliceAdvice_eq]
  have h := length_encodeList_le (List.ofFn fun i =>
    pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true)) (3 * L + 2)
      (by
        intro c hc
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
        rw [length_pairEncode, List.length_replicate, List.length_replicate]
        have hi := hfit i
        omega)
  have heq : 2 * (3 * L + 2) + 2 = 6 * L + 6 := by omega
  simpa only [List.length_ofFn, heq] using h

/-- On the same key/nonce seed, cutting a D4 tuple of full-width slice masks is the
encoded tuple of special ciphertexts from those slices:
`slicePost ⟨sliceAdvice n o len, encodeTupleOut (prfEncRealOut F masks t)⟩ =
  encodeList (List.ofFn fun i => spEncStr (fun _ => ⟦F t.1 (t.2 i)⟧.drop (o i))
    ⟦t.1⟧ ⟦m i⟧ ⟦t.2 i⟧)`, where `masks i = sliceMask L n (o i) ⟦m i⟧`
and every `o i+n+len i ≤ L`. No relabelling of the encryption seed is used.
[PS10, Theorem 99.2, with slices]

**Proof sketch.** Apply the total parser's encoded-list law to the descriptor/ciphertext
pairs from D4. Read the real tuple entrywise through its public reader. The pointwise XOR
encoding and the shared special-encryption slice-mask identity identify each selected body.
All equations preserve the input key and every nonce exactly. -/
theorem slicePost_tuple {n L q : ℕ}
    (F : (Fin n → Bool) → (Fin n → Bool) → (Fin L → Bool))
    (o len : Fin (q + 1) → ℕ) (hfit : ∀ i, o i + n + len i ≤ L)
    (m : (i : Fin (q + 1)) → Fin (len i) → Bool)
    (t : (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)) :
    slicePost (pairEncode (sliceAdvice n o len)
      (encodeTupleOut (prfEncRealOut F (fun i => sliceMask L n (o i) (List.ofFn (m i))) t))) =
        PrivateKeyScheme.encodeList (List.ofFn fun i =>
          spEncStr (fun _ => (List.ofFn (F t.1 (t.2 i))).drop (o i))
            (List.ofFn t.1) (List.ofFn (m i)) (List.ofFn (t.2 i))) := by
  rw [sliceAdvice_eq, encodeTupleOut_eq]
  have hp := slicePost_encode (List.ofFn fun i : Fin (q + 1) =>
    (pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true),
      pairEncode
        (List.ofFn (prfEncRealOut F (fun i => sliceMask L n (o i) (List.ofFn (m i))) t i).1)
        (List.ofFn (prfEncRealOut F (fun i => sliceMask L n (o i) (List.ofFn (m i))) t i).2)))
  simp only [List.map_ofFn] at hp
  refine hp.trans ?_
  apply congrArg PrivateKeyScheme.encodeList
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [prfEncRealOut_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, List.length_replicate,
    ← zipWith_xor_ofFn_add]
  have h := spEncStr_eq_sliceMask L (o i) (List.ofFn (F t.1 (t.2 i)))
    (List.ofFn t.1) (List.ofFn (m i)) (List.ofFn (t.2 i)) List.length_ofFn
      (by simpa only [List.length_ofFn] using hfit i)
  simpa only [List.length_ofFn] using h.symm

end TCSlib.Cryptography.SecureComputation.SliceReduction
