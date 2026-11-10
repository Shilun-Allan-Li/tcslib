/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Gadget
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Anti-cyclic branch matrices

## Main definitions

* `antiCyclic`: the integer anti-cyclic matrix whose upper row is a given vector.

## Main results

The matrix preserves coefficient subtraction. Binary branch differences give
bounded integer products on bounded digits. The power basis of a rational
cyclotomic field gives injectivity for nonzero coefficient vectors.

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

**Proof sketch.** The polynomial `X^(2^u)+1` is the cyclotomic polynomial of
order `2^(u+1)` and is irreducible over the rationals. Encode each integer vector
as coefficients in the quotient field's power basis. A row of the matrix encodes
a power of the adjoined root times the element for the original coefficient vector.
Wrapped indices introduce a minus sign because the width-th power of the root is
minus one. Summing the rows with the input coefficients identifies the transpose
action with field multiplication. Cancel the nonzero factor and read back the
integer coefficients. The transpose expresses the source's row action on column
inputs. The argument also includes width one. -/
theorem antiCyclic_mulVec_injective (u : ℕ) (v : Fin (2 ^ u) → ℤ) (hv : v ≠ 0) :
    Function.Injective
      (fun x : Fin (2 ^ u) → ℤ => (antiCyclic v).transpose.mulVec x) := by
  let width : ℕ := 2 ^ u
  have hwidth : 0 < width := Nat.two_pow_pos _
  letI : NeZero width := ⟨hwidth.ne'⟩
  let modulus : Polynomial ℚ := Polynomial.X ^ width + 1
  have hirred : Irreducible modulus := by
    have hcyclotomic : Polynomial.cyclotomic (2 ^ (u + 1)) ℚ = modulus := by
      rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum (n := u) Nat.prime_two,
        Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
      exact add_comm _ _
    rw [← hcyclotomic]
    exact Polynomial.cyclotomic.irreducible_rat (Nat.two_pow_pos _)
  letI : Fact (Irreducible modulus) := ⟨hirred⟩
  let K := AdjoinRoot modulus
  let root : K := AdjoinRoot.root modulus
  have root_pow : root ^ width = -1 := by
    have h : AdjoinRoot.mk modulus modulus = 0 := AdjoinRoot.mk_self
    change AdjoinRoot.mk modulus (Polynomial.X ^ width + 1) = 0 at h
    rw [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
    exact eq_neg_of_add_eq_zero_left h

  -- Read the coefficients through the quotient's existing power basis.
  have hmonic : modulus.Monic := by
    change ((Polynomial.X : Polynomial ℚ) ^ width + 1).Monic
    rw [← Polynomial.C_1]
    exact Polynomial.monic_X_pow_add_C (1 : ℚ) hwidth.ne'
  let powers := AdjoinRoot.powerBasis' hmonic
  have hdim : powers.dim = width := by
    change ((Polynomial.X : Polynomial ℚ) ^ width + 1).natDegree = width
    rw [← Polynomial.C_1]
    exact Polynomial.natDegree_X_pow_add_C
  let basis := powers.basis.reindex (finCongr hdim)
  have basis_apply (i : Fin width) : basis i = root ^ i.val := by
    change powers.basis.reindex (finCongr hdim) i = _
    rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, finCongr_symm, finCongr_apply_coe]
    rfl
  let encode (x : Fin width → ℤ) : K := basis.equivFun.symm (fun i => (x i : ℚ))
  have encode_injective : Function.Injective encode := by
    intro x y hxy
    have hcast : (fun i => (x i : ℚ)) = (fun i => (y i : ℚ)) :=
      basis.equivFun.symm.injective hxy
    funext i
    exact_mod_cast congrFun hcast i
  have encode_sum (x : Fin width → ℤ) : encode x = ∑ i, (x i : K) * root ^ i.val := by
    change basis.equivFun.symm (fun i => (x i : ℚ)) = _
    simp only [Module.Basis.equivFun_symm_apply, basis_apply, Algebra.smul_def, map_intCast]

  -- Wrapping the index costs a sign because the width-th power is minus one.
  have entry_shift (i j : Fin width) :
      (antiCyclic v i j : K) * root ^ j.val =
        root ^ i.val * (v (j - i) : K) * root ^ (j - i).val := by
    have hsub := Fin.intCast_val_sub_eq_sub_add_ite j i
    calc
      _ = (v (j - i) : K) * (root ^ i.val * root ^ (j - i).val) := by
        rw [antiCyclic_apply, ← pow_add]
        by_cases hij : i ≤ j
        · rw [if_pos hij] at hsub
          have hexponent : i.val + (j - i).val = j.val := by omega
          rw [if_pos hij, hexponent]
        · rw [if_neg hij] at hsub
          have hexponent : i.val + (j - i).val = width + j.val := by omega
          rw [if_neg hij, Int.cast_neg, hexponent, pow_add, root_pow]
          ring
      _ = _ := by ring
  have row_encode (i : Fin width) :
      ∑ j, (antiCyclic v i j : K) * root ^ j.val = root ^ i.val * encode v := by
    calc
      _ = root ^ i.val * ∑ j : Fin width, (v (j - i) : K) * root ^ (j - i).val := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [entry_shift, mul_assoc]
      _ = root ^ i.val * encode v := by
        rw [encode_sum v]
        exact congrArg (fun a : K => root ^ i.val * a)
          ((Equiv.subRight i).sum_comp fun j : Fin width => (v j : K) * root ^ j.val)
  have encode_product (x : Fin width → ℤ) :
      encode ((antiCyclic v).transpose.mulVec x) = encode x * encode v := by
    rw [encode_sum]
    calc
      _ = ∑ j : Fin width, ∑ i : Fin width,
          (x i : K) * ((antiCyclic v i j : K) * root ^ j.val) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        change ((↑(∑ i, antiCyclic v i j * x i) : K) * root ^ j.val) = _
        simp only [Int.cast_sum, Int.cast_mul]
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i : Fin width, (x i : K) * (∑ j, (antiCyclic v i j : K) * root ^ j.val) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
      _ = encode x * encode v := by
        rw [encode_sum x, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [row_encode, mul_assoc]

  -- Nonzero multiplication in the field cancels, then the coefficients agree.
  have encode_zero : encode 0 = 0 := by
    rw [encode_sum]
    simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero]
  have hv_field : encode v ≠ 0 :=
    fun h => hv (encode_injective (h.trans encode_zero.symm))
  intro x y hxy
  apply encode_injective
  exact mul_right_cancel₀ hv_field (by simpa only [encode_product] using congrArg encode hxy)

/-- Distinct binary branches give an injective integer anti-cyclic difference map
[PW10, Section 6.4].

**Proof sketch.** A differing Boolean coordinate has integer difference `1` or
`-1`, so the coefficient vector is nonzero. Apply `antiCyclic_mulVec_injective`. -/
theorem branch_difference_injective (u : ℕ) (v vstar : Fin (2 ^ u) → Bool)
    (h : v ≠ vstar) :
    Function.Injective (fun x : Fin (2 ^ u) → ℤ =>
      (antiCyclic (fun j => ((v j).toNat : ℤ) - ((vstar j).toNat : ℤ))).transpose.mulVec x) := by
  apply antiCyclic_mulVec_injective
  intro hzero
  apply h
  funext j
  have hj : ((v j).toNat : ℤ) - ((vstar j).toNat : ℤ) = 0 := congrFun hzero j
  have hbits : (v j).toNat = (vstar j).toNat := by exact_mod_cast sub_eq_zero.mp hj
  apply Bool.eq_iff_iff.mpr
  change (v j = true ↔ vstar j = true)
  rw [← Bool.toNat_eq_one, ← Bool.toNat_eq_one, hbits]

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
