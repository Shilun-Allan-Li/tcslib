/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Gadget

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Anti-cyclic branch matrices

## Main definitions

* `antiCyclic`: the integer anti-cyclic matrix whose upper row is a given vector.

## Main results

The matrix preserves coefficient subtraction. Binary branch differences give
bounded integer products on bounded digits. The injectivity obligations use the
power-of-two cyclotomic polynomial.

## References

* [PW10] C. Peikert, B. Waters, *Lossy Trapdoor Functions and Their Applications*,
  author version 4 June 2010, Section 6.4, printed pages 37--38.

Full rank here is over the rationals, giving injectivity on integer vectors.
It is deliberately not an assertion that the matrix is invertible modulo the LWE
modulus. The later branch construction uses a larger message modulus to recover
bounded integer messages before applying this injectivity statement.
-/

namespace TCSlib.Cryptography.TrapdoorFunctions.AllButOne

/-- Form the anti-cyclic matrix by wrapped subtraction of column and row indices,
negating entries below the diagonal [PW10, Section 6.4]. -/
def antiCyclic {w : ℕ} (v : Fin w → ℤ) : Matrix (Fin w) (Fin w) ℤ :=
  fun i j => if i ≤ j then v (j - i) else -v (j - i)

/-- The complete entry is the wrapped coefficient with the prescribed anti-cyclic sign. -/
theorem antiCyclic_apply {w : ℕ} (v : Fin w → ℤ) (i j : Fin w) :
    antiCyclic v i j = if i ≤ j then v (j - i) else -v (j - i) := rfl

/-- Anti-cyclic matrices preserve coefficient subtraction.

**Proof sketch.** Apply matrix extensionality and split the two possible index
orders. Integer negation distributes over the coefficient difference. -/
theorem antiCyclic_sub {w : ℕ} (v u : Fin w → ℤ) :
    antiCyclic (v - u) = antiCyclic v - antiCyclic u := by
  ext i j
  simp only [Matrix.sub_apply, antiCyclic_apply, Pi.sub_apply]
  split_ifs <;> ring

/-- At power-of-two width, a nonzero integer coefficient vector gives an injective
integer transpose multiplication map [PW10, Section 6.4].

**Proof sketch.** Interpret anti-cyclic multiplication as multiplication modulo
`X^(2^u)+1`. This cyclotomic polynomial is irreducible over the rationals. A nonzero
polynomial of smaller degree is a nonzero element of the quotient field, so its
multiplication map is injective. Restrict that rational map back to integer vectors.
No inverse modulo a composite integer modulus is used. -/
theorem antiCyclic_mulVec_injective (u : ℕ) (v : Fin (2 ^ u) → ℤ) (hv : v ≠ 0) :
    Function.Injective
      (fun x : Fin (2 ^ u) → ℤ => (antiCyclic v).transpose.mulVec x) := by
  sorry

/-- Distinct binary branches give an injective integer anti-cyclic difference map
[PW10, Section 6.4].

**Proof sketch.** A differing Boolean coordinate has integer difference `1` or
`-1`, so the coefficient vector is nonzero. Apply `antiCyclic_mulVec_injective`. -/
theorem branch_difference_injective (u : ℕ) (v vstar : Fin (2 ^ u) → Bool)
    (h : v ≠ vstar) :
    Function.Injective (fun x : Fin (2 ^ u) → ℤ =>
      (antiCyclic (fun j => ((v j).toNat : ℤ) - ((vstar j).toNat : ℤ))).transpose.mulVec x) := by
  sorry

/-- A binary branch-difference matrix sends bounded block digits to integer coordinates
of magnitude at most `2^u*(2^b-1)` [PW10, Section 6.4, explicit integer bound].

**Proof sketch.** Every matrix coefficient is minus one, zero or one. Each digit
is at most `2^b-1`; sum the absolute-value bounds over exactly `2^u` coordinates. -/
theorem branch_message_bound (b u : ℕ) (v vstar : Fin (2 ^ u) → Bool)
    (x : Fin (2 ^ u) → Fin (2 ^ b)) (j : Fin (2 ^ u)) :
    ((antiCyclic (fun i => ((v i).toNat : ℤ) - ((vstar i).toNat : ℤ))).transpose.mulVec
      (fun i => ((x i : ℕ) : ℤ)) j).natAbs ≤ 2 ^ u * (2 ^ b - 1) := by
  let C := antiCyclic (fun i => ((v i).toNat : ℤ) - ((vstar i).toNat : ℤ))
  change (∑ i, C i j * ((x i).val : ℤ)).natAbs ≤ _
  have hentry (i : Fin (2 ^ u)) : |C i j| ≤ 1 := by
    dsimp only [C]
    rw [antiCyclic_apply]
    split <;> cases hv : v (j - i) <;> cases hstar : vstar (j - i) <;> norm_num [hv, hstar]
  have hterm (i : Fin (2 ^ u)) : |C i j * ((x i).val : ℤ)| ≤ ((2 ^ b - 1 : ℕ) : ℤ) := by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    calc
      _ ≤ 1 * ((x i).val : ℤ) := mul_le_mul_of_nonneg_right (hentry i) (Int.natCast_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact_mod_cast (Nat.le_sub_one_of_lt (x i).isLt)
  have hsum : |∑ i, C i j * ((x i).val : ℤ)| ≤
      ((2 ^ u : ℕ) : ℤ) * ((2 ^ b - 1 : ℕ) : ℤ) := by
    calc
      _ ≤ ∑ i : Fin (2 ^ u), |C i j * ((x i).val : ℤ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (2 ^ u), ((2 ^ b - 1 : ℕ) : ℤ) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := by simp [mul_sub]
  have hcast : ((∑ i, C i j * ((x i).val : ℤ)).natAbs : ℤ) ≤
      ((2 ^ u * (2 ^ b - 1) : ℕ) : ℤ) := by
    simpa only [Int.natCast_natAbs, Nat.cast_mul] using hsum
  exact_mod_cast hcast

end TCSlib.Cryptography.TrapdoorFunctions.AllButOne
