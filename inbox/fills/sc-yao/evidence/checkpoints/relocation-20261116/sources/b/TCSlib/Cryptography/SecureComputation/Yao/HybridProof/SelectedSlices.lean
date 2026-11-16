/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SliceReconstruction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The two slice shapes in a selected-wire reduction

A selected inactive wire key can occur as an only key, an inner key, or an outer key.
Only and inner uses occupy the `(0,n)` slice of the joint pad. Outer uses occupy the
`(2n,4n+2)` slice, whose message is a precomputed inner ciphertext. All other keys and
nonces are explicit fixed parameters. The identities are pointwise in the challenge key
and nonce; they do not rely on inequality between distinct key values.

## Main definitions

* `SelectedSlices.innerMessage`: the precomputed outer-slice plaintext vector.

## Main results

* `SelectedSlices.zero_row`: an empty argument list leaves the plaintext unchanged.
* Slice identities for only, inner, and outer occurrences of the selected key.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (the inactive-key hybrid), Algorithm 157.2.
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party
  computation*, Journal of Cryptology 22(2), 2009, pp. 161–188.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices

open Complexity Turing TCSlib.Cryptography

/-- A zero-argument row is exactly its plaintext word, independently of both nonce halves.
This case contains no selected-key encryption. [PS10, Protocol 162.6] -/
theorem zero_row (E₁ E₂ : List Bool → List Bool) (n : ℕ) (o r₁ r₂ : Fin n → Bool) :
    (nestedSpecial E₁ E₂ n).enc [] o (r₁, r₂) = List.ofFn o := by
  rw [nestedSpecial_enc]

section Joint

variable {L L₂ : ℕ → ℕ}
  (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
  (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool))
  (E₁ E₂ : List Bool → List Bool)
  (hG : ∀ n (s x : Fin n → Bool),
    List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hG hGE₁ in
/-- A `(0,n)` slice ciphertext is the complete row when the selected key is the only
argument key. The unused second nonce can be fixed arbitrarily. [PS10, Theorem 163.7] -/
theorem only_row (n : ℕ) (k o r r₂ : Fin n → Bool) :
    sliceEnc G n 0 k r (List.ofFn o) = (nestedSpecial E₁ E₂ n).enc [k] o (r, r₂) := by
  rw [nestedSpecial_enc]
  exact sliceEnc_append_left hG hGE₁ n k r (by rw [List.length_ofFn])

include hG hGE₁ in
/-- If the selected key is the inner argument key, wrap its `(0,n)` challenge ciphertext
under the known first key with the fixed outer nonce. This is exactly the two-key row,
for every selected key and inner nonce. [PS10, Theorem 163.7] -/
theorem inner_row (n : ℕ) (k outer o r₁ r₂ : Fin n → Bool) :
    spEncStr E₂ (List.ofFn outer) (sliceEnc G n 0 k r₂ (List.ofFn o)) (List.ofFn r₁) =
      (nestedSpecial E₁ E₂ n).enc [outer, k] o (r₁, r₂) := by
  rw [nestedSpecial_enc, sliceEnc_append_left hG hGE₁ n k r₂ (by rw [List.length_ofFn])]

include hG hGE₂ in
/-- If the selected key is the outer argument key, its `(2n,4n+2)` slice encrypts the
inner ciphertext precomputed from the known second key and fixed inner nonce. The result
is the complete two-key row, for every selected key and outer nonce. [PS10, Theorem 163.7] -/
theorem outer_row (n : ℕ) (k inner o r₁ r₂ : Fin n → Bool) :
    sliceEnc G n (n + n) k r₁
      (spEncStr E₁ (List.ofFn inner) (List.ofFn o) (List.ofFn r₂)) =
        (nestedSpecial E₁ E₂ n).enc [k, inner] o (r₁, r₂) := by
  rw [nestedSpecial_enc, sliceEnc_append_right hG hGE₂]

end Joint

/-- A precomputed inner ciphertext of an `n`-bit output key has exactly `4n+2` bits
when `E₁` evaluates a `2n`-bit pad family. [PS10, Algorithm 157.2] -/
theorem innerCipher_length
    {G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {E₁ : List Bool → List Bool}
    (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₁ n s x)) (n : ℕ) (k o r : Fin n → Bool) :
    (spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r)).length = 4 * n + 2 := by
  have hp : (List.ofFn r).length + (List.ofFn o).length ≤
      (E₁ (pairEncode (List.ofFn k) (List.ofFn r))).length := by
    rw [hGE₁]
    simp only [List.length_ofFn, Nat.le_refl]
  rw [length_spEncStr E₁ hp]
  simp only [List.length_ofFn]
  omega

/-- View a precomputed inner ciphertext as a `4n+2`-bit message, with false padding if the
evaluator does not satisfy its prescribed pad-length contract. -/
def innerMessage (E₁ : List Bool → List Bool) (n : ℕ) (k o r : Fin n → Bool) :
    Fin (4 * n + 2) → Bool :=
  fun t => (spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r)).getD t.val false

/-- `innerMessage E₁ n k o r t` reads bit `t` of the precomputed inner ciphertext. -/
theorem innerMessage_eq (E₁ : List Bool → List Bool) (n : ℕ) (k o r : Fin n → Bool)
    (t : Fin (4 * n + 2)) :
    innerMessage E₁ n k o r t =
      (spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r)).getD t.val false := rfl

/-- Encoding the precomputed outer-slice message gives exactly the inner ciphertext,
when `E₁` evaluates its prescribed `2n`-bit pad family. -/
theorem innerMessage_ofFn
    {G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {E₁ : List Bool → List Bool}
    (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₁ n s x)) (n : ℕ) (k o r : Fin n → Bool) :
    List.ofFn (innerMessage E₁ n k o r) =
      spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r) := by
  have hlen := innerCipher_length hGE₁ n k o r
  apply List.ext_getElem (by rw [List.length_ofFn]; exact hlen.symm)
  intro j _ hj
  rw [List.getElem_ofFn, innerMessage_eq, List.getD_eq_getElem _ _ hj]

/-- Reading slot `j` from the actual slice multi-message sampler returns precisely its
slice ciphertext, for every sampled key and nonce vector. [PS10, Theorem 163.7] -/
theorem direct_sampler {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
    (E₂ : List Bool → List Bool) (n q : ℕ) (offset len : Fin (q + 1) → ℕ)
    (m : ∀ i, Fin (len i) → Bool) (k : Fin n → Bool)
    (r : Fin (q + 1) → Fin n → Bool) (j : Fin (q + 1)) :
    SliceReconstruction.row E₂ (pairEncode (sliceMultiEncDist G n q offset len m (k, r))
      (SliceReconstruction.directRecord j.val)) =
        sliceEnc G n (offset j) k (r j) (List.ofFn (m j)) := by
  rw [sliceMultiEncDist_apply, SliceReconstruction.encodeList_eq_encWords,
    SliceReconstruction.row_directRecord,
    List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]

/-- Wrapping sampler slot `j` uses the exact sampled slice ciphertext with the supplied
known outer key and fixed outer nonce. The selected challenge key is not given to wrapping.
[PS10, Theorem 163.7] -/
theorem wrapped_sampler {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
    (E₂ : List Bool → List Bool) (n q : ℕ) (offset len : Fin (q + 1) → ℕ)
    (m : ∀ i, Fin (len i) → Bool) (k : Fin n → Bool)
    (r : Fin (q + 1) → Fin n → Bool) (j : Fin (q + 1)) (outer nonce : List Bool) :
    SliceReconstruction.row E₂ (pairEncode (sliceMultiEncDist G n q offset len m (k, r))
      (SliceReconstruction.wrappedRecord j.val outer nonce)) =
        spEncStr E₂ outer (sliceEnc G n (offset j) k (r j) (List.ofFn (m j))) nonce := by
  rw [sliceMultiEncDist_apply, SliceReconstruction.encodeList_eq_encWords,
    SliceReconstruction.row_wrappedRecord,
    List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]

/-- Both selected-key slice shapes fit in the joint pad of length
`2n + (n + (4n+2))`: the `(0,n)` slice and the `(2n,4n+2)` slice.
[PS10, Theorem 163.7] -/
theorem slice_shapes_fit (n : ℕ) :
    0 + n + n ≤ (n + n) + (n + (4 * n + 2)) ∧
      (n + n) + n + (4 * n + 2) ≤ (n + n) + (n + (4 * n + 2)) := by
  omega

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedSlices
