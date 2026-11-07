/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Garbling
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Garbled circuits from the special encryption scheme (statement phase)

[PS10, §6.2.2–6.2.3]: the garbled rows are encrypted with Algorithm 157.2, "doubly encrypting each
row". This module instantiates the multi-key encryption interface of `Garbling.lean` with nested
special encryption, and proves it correct. Its wrong-key property and the combination with
Claim 159.a are in `GarblingSecurity.lean`.

**Nesting and lengths.** A row with two inputs encrypts the output key (`n` bits) under the
second input's key, then encrypts that ciphertext under the first input's key. The inner
ciphertext `⟨r, c⟩` has `2n + 2 + 2n = 4n + 2` bits (`length_spEncStr`), so the outer layer encrypts
`(4n + 2)`-bit messages, with a pad of `n + (4n + 2)` bits. [PS10] encrypts
`n`-bit messages only and leaves the nesting's lengths implicit; this is a declared deviation. A
single-input row is singly encrypted, and a constant gate's row is in the clear.

## Main definitions

* `SecureComputation.innerLen`: the inner ciphertext length `4n + 2`.
* `SecureComputation.nestedSpecial`: nested special encryption as a `MultiEnc` at parameter `n`.

## Main results

* `SecureComputation.nestedSpecial_decCorrect` (proved): nested special encryption is correct.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2–6.2.3 (book pp. 156–160).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography BoolCircuit

/-- The inner ciphertext length `4n + 2` of a nested row. -/
def innerLen : PolyExpr := .add (.mul (.const 4) .var) (.const 2)

/-- The inner ciphertext length expression is `4n+2`. -/
theorem innerLen_eq : innerLen = .add (.mul (.const 4) .var) (.const 2) := rfl

/-- **Nested special encryption at parameter `n`**: no key, the plaintext; one key,
Algorithm 157.2 with the pad `E₁` (`2n` bits); two keys, Algorithm 157.2 under the second key
with `E₁`, then under the first key with `E₂` (`n + (4n + 2)` bits). Longer key lists are
unused. -/
@[simps (config := { isSimp := false }) enc dec]
def nestedSpecial (E₁ E₂ : List Bool → List Bool) (n : ℕ) :
    MultiEnc (Fin n → Bool) (List Bool) ((Fin n → Bool) × (Fin n → Bool)) where
  enc ks o r := match ks with
    | [] => List.ofFn o
    | [k] => spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r.1)
    | [k₁, k₂] => spEncStr E₂ (List.ofFn k₁)
        (spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2)) (List.ofFn r.1)
    | _ => []
  dec ks c := match ks with
    | [] => decodeFin n c
    | [k] => (spDecStr E₁ n n (List.ofFn k) c).bind (decodeFin n)
    | [k₁, k₂] => (spDecStr E₂ n (innerLen.eval n) (List.ofFn k₁) c).bind fun c' =>
        (spDecStr E₁ n n (List.ofFn k₂) c').bind (decodeFin n)
    | _ => none

variable (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
  (E₁ E₂ : List Bool → List Bool)
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hGE₁ hGE₂ in
/-- **Nested special encryption is correct**: decryption under at most two keys inverts
encryption under them (`spDecStr_spEncStr` at each layer, with the inner ciphertext's length
`4n + 2`).

**Proof sketch.** Split by the number of keys. With no key, decoding the encoded plaintext
returns the plaintext. With one key, the evaluator specification gives a pad of length `2n`,
so special-encryption correctness removes the encryption before decoding. With two keys, the
inner ciphertext has length `4n + 2`; the second evaluator provides the pad of length
`n + (4n + 2)` required by the outer layer. Remove the outer layer, then the inner layer, and
decode the original plaintext. Longer key lists are excluded by the correctness contract. -/
theorem nestedSpecial_decCorrect (n : ℕ) : (nestedSpecial E₁ E₂ n).DecCorrect := by
  intro ks hks o r
  have hlen : ∀ v : Fin n → Bool, (List.ofFn v).length = n := fun v => List.length_ofFn
  match ks, hks with
  | [], _ =>
    show decodeFin n (List.ofFn o) = some o
    exact decodeFin_ofFn o
  | [k], _ =>
    show (spDecStr E₁ n n (List.ofFn k)
      (spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r.1))).bind (decodeFin n) = some o
    have hp : (E₁ (pairEncode (List.ofFn k) (List.ofFn r.1))).length = n + n := by
      rw [hGE₁ n k r.1, List.length_ofFn]
    rw [spDecStr_spEncStr E₁ (hlen k) (hlen o) (hlen r.1) hp]
    exact decodeFin_ofFn o
  | [k₁, k₂], _ =>
    show (spDecStr E₂ n (innerLen.eval n) (List.ofFn k₁)
      (spEncStr E₂ (List.ofFn k₁) (spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2))
        (List.ofFn r.1))).bind (fun c' =>
          (spDecStr E₁ n n (List.ofFn k₂) c').bind (decodeFin n)) = some o
    have hp₁ : (E₁ (pairEncode (List.ofFn k₂) (List.ofFn r.2))).length = n + n := by
      rw [hGE₁ n k₂ r.2, List.length_ofFn]
    have hc : (spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2)).length =
        innerLen.eval n := by
      rw [length_spEncStr E₁ (by rw [hp₁, hlen, hlen]), hlen, hlen]
      simp only [innerLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
        PolyExpr.eval_var]
      ring
    have hp₂ : (E₂ (pairEncode (List.ofFn k₁) (List.ofFn r.1))).length =
        n + innerLen.eval n := by
      rw [hGE₂ n k₁ r.1, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_var]
    rw [spDecStr_spEncStr E₂ (hlen k₁) hc (hlen r.1) hp₂, Option.bind_some,
      spDecStr_spEncStr E₁ (hlen k₂) (hlen o) (hlen r.2) hp₁]
    exact decodeFin_ofFn o
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

end TCSlib.Cryptography.SecureComputation
