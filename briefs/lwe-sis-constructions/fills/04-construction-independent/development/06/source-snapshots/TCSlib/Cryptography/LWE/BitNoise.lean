/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Noise
import TCSlib.Cryptography.Foundations.Probability
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Explicit bit-seed noise laws

## Main definitions

* `bitNoise`: the existing finite-noise bundle with an explicit fixed-length bit seed.
* `centeredValue`, `centeredNoise`: difference of two independent bit counts.

## Main results

The law equation retains seed multiplicities. The centered profile has support in
`[-t,t]`, a symmetric law and mean zero. Nontrivial claims await the statement audit.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definition 4.2.1 (the scalar error law).

The bit samplers and centered profile are disclosed finite-law repository
specializations, not exact discrete Gaussians. No hardness assumption, Gaussian
approximation, parameter computability or polynomial-time machine is inferred.
-/

namespace TCSlib.Cryptography.LWE

/-- Bundle a specified `t`-bit integer sampler as the actual finite LWE noise law
[Pei16, Definition 4.2.1, explicit finite-bit specialization]. -/
def bitNoise (t : ℕ) (f : (Fin t → Bool) → ℤ) : Noise where
  Coins := Fin t → Bool
  sample := f

/-- The seed type of `bitNoise t f` is the full type of `t`-bit words. -/
theorem bitNoise_Coins (t : ℕ) (f : (Fin t → Bool) → ℤ) :
    (bitNoise t f).Coins = (Fin t → Bool) := rfl

/-- Sampling `bitNoise t f` applies the specified function to all seed bits. -/
theorem bitNoise_sample (t : ℕ) (f : (Fin t → Bool) → ℤ) (r : Fin t → Bool) :
    (bitNoise t f).sample r = f r := rfl

/-- An output's probability is its number of bit-seed preimages divided by `2^t`.
Repeated outputs retain their multiplicities [Pei16, Definition 4.2.1, finite-law
specialization].

**Proof sketch.** Apply `uprob_eq_card_filter` to the complete bit-seed type and
evaluate its cardinality as `2^t`. This asserts the actual law, not uniform support. -/
theorem bitNoise_probability (t : ℕ) (f : (Fin t → Bool) → ℤ) (z : ℤ) :
    uprob (fun r : (bitNoise t f).Coins => (bitNoise t f).sample r = z) =
      ((Finset.univ.filter fun r : Fin t → Bool => f r = z).card : ℝ) / (2 ^ t : ℕ) := by
  classical
  simpa only [bitNoise_sample, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    using (uprob_eq_card_filter (fun r : Fin t → Bool => f r = z))

/-- Subtract the count of true bits in the second block from the count in the first.
This centered finite profile is a repository specialization of the noise-law slot
in [Pei16, Definition 4.2.1]. -/
def centeredValue (t : ℕ) (r : Fin (t + t) → Bool) : ℤ :=
  (∑ i : Fin t, ((r (Fin.castAdd t i)).toNat : ℤ)) -
    ∑ i : Fin t, ((r (Fin.natAdd t i)).toNat : ℤ)

/-- The centered output is exactly the difference of the two integer bit counts. -/
theorem centeredValue_eq (t : ℕ) (r : Fin (t + t) → Bool) :
    centeredValue t r = (∑ i : Fin t, ((r (Fin.castAdd t i)).toNat : ℤ)) -
      ∑ i : Fin t, ((r (Fin.natAdd t i)).toNat : ℤ) := rfl

/-- The centered-noise bundle uses exactly `t+t` independent fair seed bits. -/
def centeredNoise (t : ℕ) : Noise := bitNoise (t + t) (centeredValue t)

/-- The centered-noise bundle is the explicit two-block bit-noise instance. -/
theorem centeredNoise_eq (t : ℕ) :
    centeredNoise t = bitNoise (t + t) (centeredValue t) := rfl

/-- The centered sampler uses exactly the full pair of `t`-bit seed blocks. -/
theorem centeredNoise_Coins (t : ℕ) :
    (centeredNoise t).Coins = (Fin (t + t) → Bool) := rfl

/-- The centered sampler's sample projection is exactly its integer two-count difference. -/
theorem centeredNoise_sample (t : ℕ) (r : Fin (t + t) → Bool) :
    (centeredNoise t).sample r = centeredValue t r := rfl

/-- Every centered-noise output has absolute value at most `t`.

**Proof sketch.** Each bit count lies between zero and `t`. Their integer difference
lies in `[-t,t]`, including the empty two-block seed at `t=0`. -/
theorem centeredNoise_bounded (t : ℕ) : (centeredNoise t).Bounded t := by
  rw [Noise.bounded_iff]
  intro r
  rw [centeredNoise_sample, centeredValue_eq]
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  have hnonneg (g : Fin t → Bool) :
      0 ≤ ∑ i : Fin t, ((g i).toNat : ℤ) :=
    Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hle (g : Fin t → Bool) :
      (∑ i : Fin t, ((g i).toNat : ℤ)) ≤ (t : ℤ) := by
    calc
      (∑ i : Fin t, ((g i).toNat : ℤ)) ≤ ∑ _i : Fin t, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => Int.ofNat_le.mpr (Bool.toNat_le (g i)))
      _ = (t : ℤ) := by simp
  exact abs_sub_le_of_nonneg_of_le
    (hnonneg (fun i => r (Fin.castAdd t i)))
    (hle (fun i => r (Fin.castAdd t i)))
    (hnonneg (fun i => r (Fin.natAdd t i)))
    (hle (fun i => r (Fin.natAdd t i)))

/-- Negating an output preserves its probability under the centered profile.

**Proof sketch.** Complement every seed bit by an involution. Each block count
becomes `t` minus its old count, so their difference is negated. Relabeling the
uniform seed preserves each event probability. -/
theorem centeredValue_symmetric (t : ℕ) (z : ℤ) :
    uprob (fun r : Fin (t + t) → Bool => centeredValue t r = z) =
      uprob (fun r : Fin (t + t) → Bool => centeredValue t r = -z) := by
  let e : (Fin (t + t) → Bool) ≃ (Fin (t + t) → Bool) :=
    Function.Involutive.toPerm (fun r : Fin (t + t) → Bool => fun i => !(r i))
      (by intro r; funext i; exact Bool.not_not (r i))
  have he (r : Fin (t + t) → Bool) (i : Fin (t + t)) : e r i = !(r i) := rfl
  have hbit (b : Bool) : ((!b).toNat : ℤ) = 1 - (b.toNat : ℤ) := by
    cases b <;> decide
  have hn (r : Fin (t + t) → Bool) :
      centeredValue t (e r) = -centeredValue t r := by
    rw [centeredValue_eq, centeredValue_eq]
    simp_rw [he, hbit]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, sub_sub_sub_cancel_left, neg_sub]
  simpa only [hn, neg_inj] using
    (uprob_comp_equiv e (fun r : Fin (t + t) → Bool => centeredValue t r = -z))

/-- The centered profile has exactly zero real expectation.

**Proof sketch.** Distribute both integer bit counts and interchange the finite
sums. A coordinate permutation identifies the uniform sums for any two positions,
so the corresponding contributions from the two blocks cancel. -/
theorem centeredValue_mean (t : ℕ) :
    uexp (fun r : Fin (t + t) → Bool => (centeredValue t r : ℝ)) = 0 := by
  classical
  have hcoord (a b : Fin (t + t)) :
      (∑ r : Fin (t + t) → Bool, ((r a).toNat : ℝ)) =
        ∑ r : Fin (t + t) → Bool, ((r b).toNat : ℝ) := by
    let e := Equiv.arrowCongr (Equiv.swap a b) (Equiv.refl Bool)
    have h := e.sum_comp (fun r : Fin (t + t) → Bool => ((r b).toNat : ℝ))
    simpa only [e, Equiv.arrowCongr_apply, Equiv.refl_apply,
      Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_right] using h
  have hz : (∑ r : Fin (t + t) → Bool, (centeredValue t r : ℝ)) = 0 := by
    simp only [centeredValue_eq, Int.cast_sub, Int.cast_sum,
      Int.cast_natCast, Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    calc
      (∑ r : Fin (t + t) → Bool, ∑ i : Fin t,
          ((r (Fin.castAdd t i)).toNat : ℝ)) =
        ∑ i : Fin t, ∑ r : Fin (t + t) → Bool,
          ((r (Fin.castAdd t i)).toNat : ℝ) := Finset.sum_comm
      _ = ∑ i : Fin t, ∑ r : Fin (t + t) → Bool,
          ((r (Fin.natAdd t i)).toNat : ℝ) :=
        Finset.sum_congr rfl (fun i _ => hcoord (Fin.castAdd t i) (Fin.natAdd t i))
      _ = ∑ r : Fin (t + t) → Bool, ∑ i : Fin t,
          ((r (Fin.natAdd t i)).toNat : ℝ) := Finset.sum_comm
  rw [uexp_def, hz, zero_div]

end TCSlib.Cryptography.LWE
