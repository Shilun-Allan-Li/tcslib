/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Gadget
import Mathlib.Data.Finset.Image

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concealed gadgets: deterministic inversion and lossy image bounds

## Main definitions

* `conceal`: hide an integer error matrix behind an ordinary secret matrix product.
* `evaluate`, `residual`: binary matrix evaluation and cancellation using that secret.
* `injectiveKey`, `recover`: add a scaled gadget and recover its digits by rounding.

## Main results

Bounded entry errors give perfect inversion and injectivity for every key. Without
the gadget, evaluation factors through the public product and a bounded integer
error vector, giving an explicit image-cardinality bound. All nontrivial claims are
admitted and do not constitute an instantiated lossy-TDF security theorem.

## References

* [PW10] C. Peikert, B. Waters, *Lossy Trapdoor Functions and Their Applications*,
  author version 4 June 2010, Sections 6.2--6.3, printed pages 33--36.

This bounded-noise dyadic adaptation uses no short basis, Gaussian sampling or lattice
reduction. The trapdoor is exactly the retained matrix `T`. Concealer pseudorandomness,
its independent-secret column hybrids, polynomial machines and CCA2 consumers remain
separate obligations. In particular no unproved hardness is inferred from image loss.
-/

namespace TCSlib.Cryptography.TrapdoorFunctions.Lossy

/-- Conceal an integer error matrix as `A*T.transpose + E` modulo `q`
[PW10, Section 6.2, transposed convention]. -/
def conceal {q N d w : ℕ} [NeZero q]
    (A : Matrix (Fin N) (Fin d) (ZMod q))
    (T : Matrix (Fin w) (Fin d) (ZMod q))
    (E : Matrix (Fin N) (Fin w) ℤ) : Matrix (Fin N) (Fin w) (ZMod q) :=
  A * T.transpose + fun i j => (E i j : ZMod q)

/-- The complete concealed matrix is the ordinary secret product plus entrywise cast errors. -/
theorem conceal_eq {q N d w : ℕ} [NeZero q]
    (A : Matrix (Fin N) (Fin d) (ZMod q))
    (T : Matrix (Fin w) (Fin d) (ZMod q)) (E : Matrix (Fin N) (Fin w) ℤ) :
    conceal A T E = A * T.transpose + fun i j => (E i j : ZMod q) := rfl

/-- Evaluate both public matrix blocks on a binary input
[PW10, Section 6.3, transposed convention]. -/
def evaluate {q N d w : ℕ} [NeZero q]
    (pk : Matrix (Fin N) (Fin d) (ZMod q) × Matrix (Fin N) (Fin w) (ZMod q))
    (x : Fin N → Bool) : (Fin d → ZMod q) × (Fin w → ZMod q) :=
  (pk.1.transpose.mulVec (fun i => ((x i).toNat : ZMod q)),
    pk.2.transpose.mulVec (fun i => ((x i).toNat : ZMod q)))

/-- The first evaluation component is the binary product with the first matrix transpose. -/
theorem evaluate_fst {q N d w : ℕ} [NeZero q]
    (pk : Matrix (Fin N) (Fin d) (ZMod q) × Matrix (Fin N) (Fin w) (ZMod q))
    (x : Fin N → Bool) :
    (evaluate pk x).1 = pk.1.transpose.mulVec (fun i => ((x i).toNat : ZMod q)) := rfl

/-- The second evaluation component is the binary product with the second matrix transpose. -/
theorem evaluate_snd {q N d w : ℕ} [NeZero q]
    (pk : Matrix (Fin N) (Fin d) (ZMod q) × Matrix (Fin N) (Fin w) (ZMod q))
    (x : Fin N → Bool) :
    (evaluate pk x).2 = pk.2.transpose.mulVec (fun i => ((x i).toNat : ZMod q)) := rfl

/-- Remove the hidden ordinary secret product from the second evaluation component
[PW10, Section 6.3]. -/
def residual {q d w : ℕ} [NeZero q] (T : Matrix (Fin w) (Fin d) (ZMod q))
    (z : (Fin d → ZMod q) × (Fin w → ZMod q)) : Fin w → ZMod q :=
  z.2 - T.mulVec z.1

/-- The complete residual is the second output minus the retained matrix times the first. -/
theorem residual_eq {q d w : ℕ} [NeZero q] (T : Matrix (Fin w) (Fin d) (ZMod q))
    (z : (Fin d → ZMod q) × (Fin w → ZMod q)) :
    residual T z = z.2 - T.mulVec z.1 := rfl

/-- Add the exact scaled binary gadget to the concealed matrix
[PW10, Section 6.3, deterministic dyadic adaptation]. -/
def injectiveKey (b a w d : ℕ)
    (A : Matrix (Fin (w * b)) (Fin d) (ZMod (2 ^ (b + a))))
    (T : Matrix (Fin w) (Fin d) (ZMod (2 ^ (b + a))))
    (E : Matrix (Fin (w * b)) (Fin w) ℤ) :
    Matrix (Fin (w * b)) (Fin d) (ZMod (2 ^ (b + a))) ×
      Matrix (Fin (w * b)) (Fin w) (ZMod (2 ^ (b + a))) :=
  (A, conceal A T E + fun i j => encode b a (gadget b w i j : ZMod (2 ^ b)))

/-- The complete injective key adds the entrywise encoded gadget to the concealed block. -/
theorem injectiveKey_eq (b a w d : ℕ)
    (A : Matrix (Fin (w * b)) (Fin d) (ZMod (2 ^ (b + a))))
    (T : Matrix (Fin w) (Fin d) (ZMod (2 ^ (b + a))))
    (E : Matrix (Fin (w * b)) (Fin w) ℤ) :
    injectiveKey b a w d A T E =
      (A, conceal A T E + fun i j => encode b a (gadget b w i j : ZMod (2 ^ b))) := rfl

/-- Recover the binary input by secret cancellation, scalar rounding, and the inverse
of the existing block equivalence [PW10, Section 6.3, dyadic adaptation]. -/
def recover (b a w d : ℕ) (T : Matrix (Fin w) (Fin d) (ZMod (2 ^ (b + a))))
    (z : (Fin d → ZMod (2 ^ (b + a))) × (Fin w → ZMod (2 ^ (b + a)))) :
    Fin (w * b) → Bool :=
  (Randomized.blocksEquiv w b).symm
    (fun j => (ZMod.finEquiv (2 ^ b)).symm (decode b a (residual T z j)))

/-- The complete recovery map rounds each cancelled coordinate and inverts block packing. -/
theorem recover_eq (b a w d : ℕ) (T : Matrix (Fin w) (Fin d) (ZMod (2 ^ (b + a))))
    (z : (Fin d → ZMod (2 ^ (b + a))) × (Fin w → ZMod (2 ^ (b + a)))) :
    recover b a w d T z = (Randomized.blocksEquiv w b).symm
      (fun j => (ZMod.finEquiv (2 ^ b)).symm (decode b a (residual T z j))) := rfl

/-- A concealed evaluation leaves exactly the original integer error subset sum.

**Proof sketch.** Expand using public matrix multiplication and evaluation equations,
interchange finite sums, and cancel the two secret-product terms. Cast the remaining
integer sum without discarding its sign. -/
theorem residual_conceal {q N d w : ℕ} [NeZero q]
    (A : Matrix (Fin N) (Fin d) (ZMod q)) (T : Matrix (Fin w) (Fin d) (ZMod q))
    (E : Matrix (Fin N) (Fin w) ℤ) (x : Fin N → Bool) (j : Fin w) :
    residual T (evaluate (A, conceal A T E) x) j =
      ((∑ i, E i j * ((x i).toNat : ℤ) : ℤ) : ZMod q) := by
  sorry

/-- With the gadget present, cancellation leaves its encoded digit plus the same
original integer error sum [PW10, Section 6.3, exact-divisibility adaptation].

**Proof sketch.** Use `residual_conceal` for the concealed terms. The gadget's selected
sum commutes with the additive exact encoder; `gadget_mulVec` identifies its digit. -/
theorem residual_injectiveKey (b a w d : ℕ)
    (A : Matrix (Fin (w * b)) (Fin d) (ZMod (2 ^ (b + a))))
    (T : Matrix (Fin w) (Fin d) (ZMod (2 ^ (b + a))))
    (E : Matrix (Fin (w * b)) (Fin w) ℤ) (x : Fin (w * b) → Bool) (j : Fin w) :
    residual T (evaluate (injectiveKey b a w d A T E) x) j =
      encode b a (digits b w x j : ZMod (2 ^ b)) +
        ((∑ i, E i j * ((x i).toNat : ℤ) : ℤ) : ZMod (2 ^ (b + a))) := by
  sorry

/-- A selected integer error column has absolute sum at most `N*B`.

**Proof sketch.** Each binary multiplier is zero or one. Apply the integer triangle
inequality and add the `N` coordinatewise bounds. -/
theorem error_sum_bound {N w : ℕ} (E : Matrix (Fin N) (Fin w) ℤ)
    (x : Fin N → Bool) (B : ℕ) (hE : ∀ i j, (E i j).natAbs ≤ B) (j : Fin w) :
    (∑ i, E i j * ((x i).toNat : ℤ)).natAbs ≤ N * B := by
  sorry

/-- The retained ordinary secret matrix perfectly recovers every input for every
bounded-error key under strict rounding separation [PW10, Section 6.3, refinement].

**Proof sketch.** Combine `residual_injectiveKey` and `error_sum_bound`. Apply
`decode_encode_add` coordinatewise under `2*(w*b*B)<2^a`, then invert the existing
block equivalence. There is no bad-key event or omitted Gaussian tail. -/
theorem recover_evaluate (b a w d : ℕ) (ha : 0 < a)
    (A : Matrix (Fin (w * b)) (Fin d) (ZMod (2 ^ (b + a))))
    (T : Matrix (Fin w) (Fin d) (ZMod (2 ^ (b + a))))
    (E : Matrix (Fin (w * b)) (Fin w) ℤ) (B : ℕ)
    (hE : ∀ i j, (E i j).natAbs ≤ B) (hsep : 2 * (w * b * B) < 2 ^ a)
    (x : Fin (w * b) → Bool) :
    recover b a w d T (evaluate (injectiveKey b a w d A T E) x) = x := by
  sorry

/-- Every bounded-noise gadget key defines an injective function under the same
separation condition [PW10, Section 6.3, perfect-inversion adaptation].

**Proof sketch.** Apply the left inverse `recover_evaluate` to any equal evaluations. -/
theorem evaluate_injective (b a w d : ℕ) (ha : 0 < a)
    (A : Matrix (Fin (w * b)) (Fin d) (ZMod (2 ^ (b + a))))
    (T : Matrix (Fin w) (Fin d) (ZMod (2 ^ (b + a))))
    (E : Matrix (Fin (w * b)) (Fin w) ℤ) (B : ℕ)
    (hE : ∀ i j, (E i j).natAbs ≤ B) (hsep : 2 * (w * b * B) < 2 ^ a) :
    Function.Injective (evaluate (injectiveKey b a w d A T E)) := by
  sorry

/-- A key without the gadget has image size at most `q^d*(2*N*B+1)^w`
[PW10, Section 6.3, explicit bounded-integer image adaptation].

**Proof sketch.** Factor evaluation through its first modular product and the
integer vector of error subset sums. Each integer coordinate lies in `[-N*B,N*B]`,
which has `2*N*B+1` values. Count the product of these finite ranges. Reduction
modulo `q` may identify more outputs and cannot increase this upper bound. -/
theorem lossy_range_card {q N d w : ℕ} [NeZero q]
    (A : Matrix (Fin N) (Fin d) (ZMod q)) (T : Matrix (Fin w) (Fin d) (ZMod q))
    (E : Matrix (Fin N) (Fin w) ℤ) (B : ℕ) (hE : ∀ i j, (E i j).natAbs ≤ B) :
    (Finset.univ.image (evaluate (A, conceal A T E))).card ≤
      q ^ d * (2 * N * B + 1) ^ w := by
  sorry

/-- An explicit cardinality budget yields at least `k` bits of image loss.

**Proof sketch.** Multiply `lossy_range_card` by `2^k` and apply the supplied numeric
budget. The binary domain has exactly `2^N` elements; no hardness conclusion is used. -/
theorem lossy_bits {q N d w : ℕ} [NeZero q]
    (A : Matrix (Fin N) (Fin d) (ZMod q)) (T : Matrix (Fin w) (Fin d) (ZMod q))
    (E : Matrix (Fin N) (Fin w) ℤ) (B k : ℕ) (hE : ∀ i j, (E i j).natAbs ≤ B)
    (hbudget : q ^ d * (2 * N * B + 1) ^ w * 2 ^ k ≤ 2 ^ N) :
    (Finset.univ.image (evaluate (A, conceal A T E))).card * 2 ^ k ≤ 2 ^ N := by
  sorry

end TCSlib.Cryptography.TrapdoorFunctions.Lossy
