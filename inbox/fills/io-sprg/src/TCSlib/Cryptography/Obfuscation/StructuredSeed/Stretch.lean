/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Correctness
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import Mathlib.Algebra.Order.Floor.Semifield

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial stretch of the JLS construction

## Main definitions

* `E0` gives the explicit sufficient polynomial schedule exponent.
* `Params.seedBitsAt` is the public/private field-vector payload bit count.

## Main results

* `Params.seedBitsAt_le` bounds the payload uniformly in every public prime.
* `jls_seedBits_le` reads the same bound on the raw construction.
* `jls_hasPolyStretch` states Claim 4.1 for the fixed polynomial schedule.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026,
  Claim 4.1 and its proof, p. 18.

Dv1 fixes one security parameter and a polynomial input-length schedule. Dv2 counts
field-vector payload bits; Dv3 fixes exact integral rounding; Dv5 uses the Boolean
stretch lower bound. The explicit threshold uses a generous fifth-power payload bound.
The rational noise exponent is coerced to real values in these analytic bounds.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

/-- A sufficient schedule exponent is
`E0 d delta tau = floor(max(10/delta,5/(tau-1)))+1`.
[JLS26, Claim 4.1, p. 18]. Dv1 makes sufficiently large polynomial seed length an
explicit condition on E. The estimate uses a deliberately generous fifth-power
seed bound; d is retained in the interface although this sufficient threshold is
independent of it when d≥1. The construction's rational noise exponent is coerced to real. -/
noncomputable def E0 (_d : ℕ) (δ τ : ℝ) : ℕ :=
  ⌊max (10 / δ) (5 / (τ - 1))⌋₊ + 1

/-- The sufficient exponent is its stated real-power comparison threshold; glue. -/
theorem E0_eq (d : ℕ) (δ τ : ℝ) :
    E0 d δ τ = ⌊max (10 / δ) (5 / (τ - 1))⌋₊ + 1 := rfl

namespace Params

/-- The construction's seed payload has
`seedBitsAt kappa = (pubLen kappa + privLen kappa)*(kappa+1)` bits.
[JLS26, proof of Claim 4.1, p. 18]. Dv2 uses fixed-width field vectors. Dv9's
arbitrary public prime changes no width, so this count is uniform in that prime. -/
noncomputable def seedBitsAt (P : Params) (κ : ℕ) : ℕ :=
  (P.pubLen κ + P.privLen κ) * (κ + 1)

/-- The payload count is the total coordinate count times kappa+1; glue. -/
theorem seedBitsAt_eq (P : Params) (κ : ℕ) :
    P.seedBitsAt κ = (P.pubLen κ + P.privLen κ) * (κ + 1) := rfl

/-- The seed payload is at most `C*(kappa+1)^5*(n+m/w+1)` for a fixed natural C,
uniformly over every kappa and every public prime. [JLS26, proof of Claim 4.1, p. 18].
Dv1 fixes the polynomial schedule; Dv2-Dv3 replace the asymptotic expression by this
explicit integral upper bound. Natural division and the final one cover rounding
and the zero-parameter boundary. The noise exponent is rational.

**Proof sketch.** Count the repeated public vectors, flags, tensor coordinates and two
factor arrays. Bound the rounded bucket count by its quotient plus one, and cancel
one noise-width factor against W=w^2 in the factor-array term. Bound the tensor
term by a degree-dependent constant times n, absorb rounding terms using w≤ell+1,
and enlarge the fixed constant to cover the finitely many boundary cases. -/
theorem seedBitsAt_le (P : Params) :
    ∃ C : ℕ, ∀ κ,
      P.seedBitsAt κ ≤ C * (κ + 1) ^ 5 * (P.n κ + P.m κ / P.w κ + 1) := by
  refine ⟨2 * (2 ^ P.D) + 12, ?_⟩
  intro κ
  let K := κ + 1
  let X := P.n κ + P.m κ / P.w κ + 1
  let a := 2 ^ P.D
  have hK : κ ≤ K := Nat.le_add_right κ 1
  have hKpos : 0 < K := Nat.succ_pos κ
  have hX : P.n κ + 1 ≤ X := ?_
  swap
  · exact Nat.add_le_add_right (Nat.le_add_right (P.n κ) (P.m κ / P.w κ)) 1
  have htensor : (P.ℓ κ + 1) ^ P.D ≤ a * X := ?_
  swap
  · have ht := add_pow_le (Nat.zero_le (P.ℓ κ)) (Nat.zero_le 1) P.D
    have hp : 2 ^ (P.D - 1) ≤ (2 : ℕ) ^ P.D :=
      Nat.pow_le_pow_right (Nat.succ_pos 1) (Nat.sub_le P.D 1)
    have ht' := ht.trans
      (Nat.mul_le_mul_right ((P.ℓ κ) ^ P.D + 1 ^ P.D) hp)
    rw [one_pow, ← P.n_eq] at ht'
    exact ht'.trans (Nat.mul_le_mul_left a hX)
  have hwpos : 0 < P.w κ := ?_
  swap
  · rw [P.w_eq]
    exact P.noiseWidth_pos _
  have hwX : P.w κ ≤ X := ?_
  swap
  · have hw : P.w κ ≤ P.W κ := ?_
    swap
    · rw [P.W_eq]
      exact Nat.le_pow (Nat.succ_pos 1)
    have hn : P.ℓ κ ≤ P.n κ := ?_
    swap
    · rw [P.n_eq]
      exact Nat.le_pow P.D_pos
    exact hw.trans ((P.W_le_ell_add_one κ).trans
      ((Nat.add_le_add_right hn 1).trans hX))
  have hBw0 : P.B κ * P.w κ ≤ κ * (P.m κ / P.w κ + 1) + P.w κ := ?_
  swap
  · have hW : 0 < P.W κ := P.W_pos κ
    have hB : P.B κ ≤ P.m κ * κ / P.W κ + 1 := ?_
    swap
    · rw [P.B_eq, P.t_eq]
      apply max_le
      · exact Nat.succ_le_succ (Nat.zero_le _)
      · exact (Nat.div_le_div_right (Nat.sub_le _ _)).trans_eq
          (Nat.add_div_right _ hW)
    have hBw : P.B κ * P.w κ ≤
        (P.m κ * κ / P.w κ) / P.w κ * P.w κ + P.w κ := ?_
    swap
    · convert Nat.mul_le_mul_right (P.w κ) hB using 1
      rw [P.W_eq, pow_two, ← Nat.div_div_eq_div_mul, add_mul, one_mul]
    have hm : P.m κ * κ ≤ (κ * (P.m κ / P.w κ + 1)) * P.w κ := ?_
    swap
    · have hm' := Nat.mul_le_mul_right κ
        (Nat.lt_mul_div_succ (P.m κ) hwpos).le
      nlinarith
    have hq : P.m κ * κ / P.w κ ≤ κ * (P.m κ / P.w κ + 1) :=
      (Nat.div_le_div_right hm).trans_eq (Nat.mul_div_left _ hwpos)
    exact hBw.trans ((Nat.add_le_add_right
      (Nat.div_mul_le_self (P.m κ * κ / P.w κ) (P.w κ)) (P.w κ)).trans
        (Nat.add_le_add_right hq (P.w κ)))
  have hqX : P.m κ / P.w κ + 1 ≤ X := ?_
  swap
  · dsimp only [X]
    omega
  have hBw : P.B κ * P.w κ ≤ 2 * K * X := ?_
  swap
  · have hmul := Nat.mul_le_mul hK hqX
    have hXK : X ≤ K * X := Nat.le_mul_of_pos_left X hKpos
    nlinarith
  have hκsq : κ ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left hK 2
  have hfactors : P.B κ * (P.rc κ * P.t κ + P.t κ * P.rc κ) ≤
      4 * K ^ 3 * X := ?_
  swap
  · have heq : P.B κ * (P.rc κ * P.t κ + P.t κ * P.rc κ) =
        2 * κ ^ 2 * (P.B κ * P.w κ) := ?_
    swap
    · rw [P.rc_eq, P.t_eq]
      ring
    have h1 := Nat.mul_le_mul_left (2 * κ ^ 2) hBw
    have h2 := Nat.mul_le_mul_right (4 * K * X) hκsq
    rw [heq]
    nlinarith
  have hsLen : P.sLen κ ≤ (a + 4) * K ^ 3 * X := ?_
  swap
  · have htK := Nat.mul_le_mul_left a
      (Nat.le_mul_of_pos_left X (pow_pos hKpos 3))
    rw [P.sLen_eq]
    nlinarith
  have hbase : κ * P.n κ + 1 + κ ≤ K * X := ?_
  swap
  · have hmul := Nat.mul_le_mul_left K hX
    dsimp only [K] at hmul ⊢
    nlinarith
  have hrest : 2 * κ * P.sLen κ ≤ 2 * (a + 4) * K ^ 4 * X := ?_
  swap
  · have h1 := Nat.mul_le_mul_left (2 * κ) hsLen
    have h2 := Nat.mul_le_mul_right (2 * (a + 4) * K ^ 3 * X) hK
    nlinarith
  have hK4 : K ≤ K ^ 4 := Nat.le_self_pow (Nat.succ_ne_zero 3) K
  have hcount : P.pubLen κ + P.privLen κ ≤ (2 * a + 12) * K ^ 4 * X := ?_
  swap
  · have hbase4 := Nat.mul_le_mul_right X hK4
    have hmargin := Nat.zero_le (K ^ 4 * X)
    rw [P.pubLen_eq, P.privLen_eq]
    nlinarith
  have hbits := Nat.mul_le_mul_right K hcount
  rw [P.seedBitsAt_eq]
  convert hbits using 1
  dsimp only [K, X, a]
  ring

end Params

namespace Internal

/-- At every κ≥1, rounded noise width is at least half of κ^(E*δ/2).
[JLS26, proof of Claim 4.1, p. 18]. This is glue for the integral noise schedule.

**Proof sketch.** Read the width and dimension equations, combine the two real powers,
then apply the public half-of-a-real lower bound for its natural floor. The power is
at least one, so max-one rounding does not decrease the bound. -/
theorem w_lower (P : Params) (κ : ℕ) (hκ : 1 ≤ κ) :
    (κ : ℝ) ^ ((P.E : ℝ) * ((P.δ : ℝ) / 2)) / 2 ≤ (P.w κ : ℝ) := by
  rw [P.w_eq, P.noiseWidth_eq, P.ℓ_eq, Nat.cast_pow,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg κ) P.E ((P.δ : ℝ) / 2)]
  have hb : 0 ≤ (P.E : ℝ) * ((P.δ : ℝ) / 2) :=
    mul_nonneg (Nat.cast_nonneg P.E)
      (div_nonneg (Rat.cast_nonneg.mpr P.δ_pos.le) zero_le_two)
  have hx : 1 ≤ (κ : ℝ) ^ ((P.E : ℝ) * ((P.δ : ℝ) / 2)) :=
    Real.one_le_rpow (Nat.one_le_cast.mpr hκ) hb
  have hf : 1 ≤ ⌊(κ : ℝ) ^ ((P.E : ℝ) * ((P.δ : ℝ) / 2))⌋₊ :=
    (Nat.one_le_floor_iff _).mpr hx
  rw [max_eq_right hf]
  exact (Nat.div_two_lt_floor hx).le

/-- The sufficient E0 threshold leaves positive exponent gaps for public and noise terms.
[JLS26, proof of Claim 4.1, p. 18]. The integral threshold makes both gaps strict.

**Proof sketch.** The real threshold is below its natural floor plus one, hence below E.
Multiply its two components by positive δ and τ−1, and use D≥1 for the public term. -/
theorem stretch_gaps (P : Params) {τ : ℝ} (hτ : 1 < τ)
    (hE : E0 P.d (P.δ : ℝ) τ ≤ P.E) :
    0 < (((P.E * P.D : ℕ) : ℝ) * (τ - 1) - 5) ∧
      0 < (P.E : ℝ) * ((P.δ : ℝ) / 2) - 5 := by
  rw [E0_eq] at hE
  have hc : (⌊max (10 / (P.δ : ℝ)) (5 / (τ - 1))⌋₊ : ℝ) + 1 ≤ (P.E : ℝ) := ?_
  swap
  · exact_mod_cast hE
  have hm : max (10 / (P.δ : ℝ)) (5 / (τ - 1)) < (P.E : ℝ) :=
    (Nat.lt_floor_add_one _).trans_le hc
  have hδ : 0 < (P.δ : ℝ) := Rat.cast_pos.mpr P.δ_pos
  have hτ' : 0 < τ - 1 := sub_pos.mpr hτ
  have h10 : 10 < (P.E : ℝ) * (P.δ : ℝ) :=
    (div_lt_iff₀ hδ).mp ((le_max_left _ _).trans_lt hm)
  have h5 : 5 < (P.E : ℝ) * (τ - 1) :=
    (div_lt_iff₀ hτ').mp ((le_max_right _ _).trans_lt hm)
  have ha : (P.E : ℝ) ≤ ((P.E * P.D : ℕ) : ℝ) := ?_
  swap
  · exact_mod_cast (Nat.le_mul_of_pos_right P.E P.D_pos)
  have hmul := mul_le_mul_of_nonneg_right ha hτ'.le
  constructor <;> nlinarith

/-- Positive public/noise exponent gaps give seedBitsAt ≤ m*κ^(-ε) eventually.
[JLS26, proof of Claim 4.1, p. 18]. This quantitative glue keeps the rounded width
and the fixed payload coefficient explicit, uniformly over public prime schedules.

**Proof sketch.** Write n=κ^a and use Boolean stretch to lower-bound m by κ^(aτ).
The width lower bound controls floor(m/w). Compare the public, noise and constant
terms after κ^5 with m*κ^(-2ε), and bound (κ+1)^5 by 32κ^5. Their sum is bounded
by 128*C*m*κ^(-2ε). The public real-power limit absorbs 128*C into κ^ε beyond
one cutoff, giving the claimed relative gap. -/
theorem eventually_seed_relative_gap (P : Params) {τ ε : ℝ}
    (hs : P.G.HasStretch τ) (hε : 0 < ε)
    (hpublic : 5 + ((P.E * P.D : ℕ) : ℝ) + 2 * ε ≤
      ((P.E * P.D : ℕ) : ℝ) * τ)
    (hnoise : 5 - (P.E : ℝ) * ((P.δ : ℝ) / 2) ≤ -2 * ε) :
    ∀ᶠ κ : ℕ in Filter.atTop,
      (P.seedBitsAt κ : ℝ) ≤ (P.m κ : ℝ) * (κ : ℝ) ^ (-ε) := by
  obtain ⟨C, hseedNat⟩ := P.seedBitsAt_le
  let a : ℝ := ((P.E * P.D : ℕ) : ℝ)
  let b : ℝ := (P.E : ℝ) * ((P.δ : ℝ) / 2)
  change 5 + a + 2 * ε ≤ a * τ at hpublic
  change 5 - b ≤ -2 * ε at hnoise
  have hgrow : ∀ᶠ κ : ℕ in Filter.atTop,
      128 * (C : ℝ) ≤ (κ : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), hgrow] with κ hκ hC
  let x : ℝ := κ
  have hx1 : 1 ≤ x := Nat.one_le_cast.mpr hκ
  have hxpos : 0 < x := zero_lt_one.trans_le hx1
  have hx0 : 0 ≤ x := hxpos.le
  have hn : (P.n κ : ℝ) = x ^ a := ?_
  swap
  · dsimp only [a, x]
    rw [Real.rpow_natCast, P.n_eq, P.ℓ_eq, Nat.cast_pow, Nat.cast_pow, pow_mul]
  have hm : x ^ (a * τ) ≤ (P.m κ : ℝ) := ?_
  swap
  · have h := (P.G.hasStretch_iff τ).mp hs (P.n κ)
    rw [hn, ← Real.rpow_mul hx0, ← P.m_eq] at h
    exact h
  have hw : x ^ b / 2 ≤ (P.w κ : ℝ) := w_lower P κ hκ
  have hwpos : (0 : ℝ) < P.w κ := ?_
  swap
  · rw [P.w_eq]
    exact Nat.cast_pos.mpr (P.noiseWidth_pos _)
  have hdiv : ((P.m κ / P.w κ : ℕ) : ℝ) ≤
      2 * (P.m κ : ℝ) * x ^ (-b) := ?_
  swap
  · calc
      _ ≤ (P.m κ : ℝ) / (P.w κ : ℝ) := Nat.cast_div_le
      _ ≤ (P.m κ : ℝ) / (x ^ b / 2) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _)
          (half_pos (Real.rpow_pos_of_pos hxpos b)) hw
      _ = 2 * (P.m κ : ℝ) * x ^ (-b) := ?_
    rw [Real.rpow_neg hx0]
    field_simp [(Real.rpow_pos_of_pos hxpos b).ne']
  have hexp : 5 + a ≤ a * τ + (-2 * ε) := ?_
  swap
  · linarith
  have hnterm : x ^ 5 * (P.n κ : ℝ) ≤ (P.m κ : ℝ) * x ^ (-2 * ε) := ?_
  swap
  · calc
      _ = x ^ ((5 : ℝ) + a) := ?_
      _ ≤ x ^ (a * τ + (-2 * ε)) :=
        Real.rpow_le_rpow_of_exponent_le hx1 hexp
      _ = x ^ (a * τ) * x ^ (-2 * ε) := Real.rpow_add hxpos _ _
      _ ≤ (P.m κ : ℝ) * x ^ (-2 * ε) :=
        mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hx0 _)
    rw [hn, ← Real.rpow_natCast x 5, ← Real.rpow_add hxpos, Nat.cast_ofNat]
  have hnoisePow : x ^ 5 * x ^ (-b) ≤ x ^ (-2 * ε) := ?_
  swap
  · rw [← Real.rpow_natCast x 5, ← Real.rpow_add hxpos, Nat.cast_ofNat]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    linarith
  have hnoiseTerm := mul_le_mul_of_nonneg_left hnoisePow (Nat.cast_nonneg (P.m κ))
  have hn1 : 1 ≤ (P.n κ : ℝ) := ?_
  swap
  · rw [hn]
    exact Real.one_le_rpow hx1 (Nat.cast_nonneg (P.E * P.D))
  have hconst : x ^ 5 ≤ (P.m κ : ℝ) * x ^ (-2 * ε) := ?_
  swap
  · calc
      x ^ 5 = x ^ 5 * 1 := (mul_one _).symm
      _ ≤ x ^ 5 * (P.n κ : ℝ) :=
        mul_le_mul_of_nonneg_left hn1 (pow_nonneg hx0 5)
      _ ≤ (P.m κ : ℝ) * x ^ (-2 * ε) := hnterm
  have hcombined : x ^ 5 * ((P.n κ : ℝ) +
      2 * (P.m κ : ℝ) * x ^ (-b) + 1) ≤
      4 * (P.m κ : ℝ) * x ^ (-2 * ε) := ?_
  swap
  · nlinarith
  have hκ2 : ((κ + 1 : ℕ) : ℝ) ≤ 2 * x := ?_
  swap
  · push_cast
    change x + 1 ≤ 2 * x
    linarith
  have hK5 := pow_le_pow_left₀ (Nat.cast_nonneg (κ + 1)) hκ2 5
  norm_num [mul_pow] at hK5
  have hseed : (P.seedBitsAt κ : ℝ) ≤
      (C : ℝ) * ((κ + 1 : ℕ) : ℝ) ^ 5 *
        ((P.n κ : ℝ) + ((P.m κ / P.w κ : ℕ) : ℝ) + 1) := ?_
  swap
  · exact_mod_cast (hseedNat κ)
  push_cast at hseed
  have hsum : (P.n κ : ℝ) + ((P.m κ / P.w κ : ℕ) : ℝ) + 1 ≤
      (P.n κ : ℝ) + 2 * (P.m κ : ℝ) * x ^ (-b) + 1 :=
    add_le_add_right (add_le_add_left hdiv _) 1
  have hpre := mul_le_mul_of_nonneg_left hK5 (Nat.cast_nonneg C)
  have hsum0 : (0 : ℝ) ≤
      (P.n κ : ℝ) + ((P.m κ / P.w κ : ℕ) : ℝ) + 1 := ?_
  swap
  · positivity
  have hpre0 : (0 : ℝ) ≤ (C : ℝ) * (32 * x ^ 5) := ?_
  swap
  · positivity
  have hfirst := mul_le_mul hpre hsum hsum0 hpre0
  have hC32 : (0 : ℝ) ≤ 32 * (C : ℝ) := ?_
  swap
  · positivity
  have hmult := mul_le_mul_of_nonneg_left hcombined hC32
  have hcoarse : (P.seedBitsAt κ : ℝ) ≤
      128 * (C : ℝ) * (P.m κ : ℝ) * x ^ (-2 * ε) := ?_
  swap
  · nlinarith [hseed]
  have hnonneg : (0 : ℝ) ≤ (P.m κ : ℝ) * x ^ (-2 * ε) := ?_
  swap
  · positivity
  have habsorb := mul_le_mul_of_nonneg_right hC hnonneg
  have hpow : x ^ ε * x ^ (-2 * ε) = x ^ (-ε) := ?_
  swap
  · rw [← Real.rpow_add hxpos]
    congr 1
    ring
  change 128 * (C : ℝ) * ((P.m κ : ℝ) * x ^ (-2 * ε)) ≤
    x ^ ε * ((P.m κ : ℝ) * x ^ (-2 * ε)) at habsorb
  rw [← mul_assoc (x ^ ε) (P.m κ : ℝ) (x ^ (-2 * ε)),
    mul_comm (x ^ ε) (P.m κ : ℝ),
    mul_assoc (P.m κ : ℝ) (x ^ ε) (x ^ (-2 * ε)), hpow] at habsorb
  nlinarith

end Internal

/-- The raw construction's seed-bit function equals the prime-independent payload count.
[JLS26, proof of Claim 4.1, p. 18]. Dv1-Dv2 and Dv9 fix the family and residue width.

**Proof sketch.** Read SPRG.Raw.seedBits through its published equation, then use the
construction's public/private length and residue-width field readers. -/
theorem jls_seedBits_eq (P : Params) (π : PrimeSchedule) (κ : ℕ) :
    (jlsSPRG_raw P π).seedBits κ = P.seedBitsAt κ := by
  rw [SPRG.Raw.seedBits_eq, jlsSPRG_raw_pubLen, jlsSPRG_raw_privLen,
    jlsSPRG_raw_residueBits, P.seedBitsAt_eq,
    Complexity.PolyExpr.eval_add, Complexity.PolyExpr.eval_var,
    Complexity.PolyExpr.eval_const]

/-- The raw construction has seed length at most
`C*(kappa+1)^5*(n+m/w+1)` at every parameter. [JLS26, proof of Claim 4.1, p. 18].
Dv1-Dv3 make the schedule, field widths and exact rounding explicit; the constant can
be chosen independently of the public prime schedule.

**Proof sketch.** Apply the prime-independent payload estimate and read the raw
construction's bit count through jls_seedBits_eq. -/
theorem jls_seedBits_le (P : Params) (π : PrimeSchedule) :
    ∃ C : ℕ, ∀ κ,
      (jlsSPRG_raw P π).seedBits κ ≤
        C * (κ + 1) ^ 5 * (P.n κ + P.m κ / P.w κ + 1) := by
  obtain ⟨C, hC⟩ := P.seedBitsAt_le
  refine ⟨C, ?_⟩
  intro κ
  rw [jls_seedBits_eq]
  exact hC κ

/-- The raw construction has polynomial stretch when its schedule exponent is at least E0.
[JLS26, Claim 4.1, p. 18]. Dv1 replaces sufficiently large polynomial seed length by
`E0 d delta tau ≤ E`; Dv3 uses rounded noise and Dv5 uses the input stretch lower bound.
The rational noise exponent is coerced to real for the threshold. Dv18 keeps this
stretch theorem on the raw bundle; honest efficiency is supplied by the later assembly.
Eventual seed growth is required as well as the power bound.

**Proof sketch.** Read the sufficient exponent to obtain E*delta/2>5 and E*(tau-1)>5.
Apply the fifth-power payload bound. The rounded noise width eventually grows like
ell^(delta/2), so both n and m/w leave a positive power gap below m after the kappa^5
factor. Use the polynomial output upper bound to choose one fixed stretch exponent
strictly above one, and absorb the fixed constant beyond a common threshold.
The public length is at least one, so its κ+1-bit residue width also gives
κ+1 ≤ seedBits at every κ and supplies the seed-growth conjunct. -/
theorem jls_hasPolyStretch (P : Params) (π : PrimeSchedule) {τ : ℝ} (hτ : 1 < τ)
    (hs : P.G.HasStretch τ) (hE : E0 P.d (P.δ : ℝ) τ ≤ P.E) :
    (jlsSPRG_raw P π).HasPolyStretch := by
  obtain ⟨hg1, hg2⟩ := Internal.stretch_gaps P hτ hE
  let a : ℝ := ((P.E * P.D : ℕ) : ℝ)
  let b : ℝ := (P.E : ℝ) * ((P.δ : ℝ) / 2)
  let ε : ℝ := min (a * (τ - 1) - 5) (b - 5) / 2
  have hε : 0 < ε := div_pos (lt_min hg1 hg2) zero_lt_two
  have hpublic : 5 + a + 2 * ε ≤ a * τ := ?_
  swap
  · have hmin := min_le_left (a * (τ - 1) - 5) (b - 5)
    dsimp only [ε]
    linarith
  have hnoise : 5 - b ≤ -2 * ε := ?_
  swap
  · have hmin := min_le_right (a * (τ - 1) - 5) (b - 5)
    dsimp only [ε]
    linarith
  obtain ⟨κs, hκs⟩ := Filter.eventually_atTop.mp
    (Internal.eventually_seed_relative_gap P hs hε hpublic hnoise)
  let q : Complexity.PolyExpr :=
    P.G.outBound.subst (Complexity.PolyExpr.pow .var (P.E * P.D))
  obtain ⟨C, c, hq⟩ := Complexity.PolyExpr.eval_le q
  let D : ℝ := max 1 ((C : ℝ) * (2 : ℝ) ^ c)
  let η : ℝ := ε / (2 * ((c + 1 : ℕ) : ℝ))
  let τ' : ℝ := 1 + η
  have hN : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos c)
  have hη : 0 < η := div_pos hε (mul_pos zero_lt_two hN)
  have hτ' : 1 < τ' := ?_
  swap
  · dsimp only [τ']
    linarith
  have hNη : (((c + 1 : ℕ) : ℝ)) * η = ε / 2 := ?_
  swap
  · dsimp only [η]
    field_simp [hN.ne']
  have hcη : (c : ℝ) * η ≤ ε / 2 := ?_
  swap
  · push_cast at hNη
    nlinarith
  have hετ : ε ≤ ε * τ' := ?_
  swap
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hτ'.le hε.le
  have hexp : ε / 2 + (c : ℝ) * η + (-ε) * τ' ≤ 0 := ?_
  swap
  · nlinarith
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hDgrow : ∀ᶠ κ : ℕ in Filter.atTop,
      D ^ η ≤ (κ : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (half_pos hε)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨κD, hκD⟩ := Filter.eventually_atTop.mp hDgrow
  rw [SPRG.Raw.hasPolyStretch_iff]
  refine ⟨τ', hτ', max 1 (max κs κD), ?_⟩
  intro κ hκ
  have hcuts : 1 ≤ κ ∧ κs ≤ κ ∧ κD ≤ κ := ?_
  swap
  · omega
  rcases hcuts with ⟨hκ1, hκs', hκD'⟩
  rw [jls_seedBits_eq, jlsSPRG_raw_outLen]
  constructor
  · rw [P.seedBitsAt_eq, P.pubLen_eq]
    exact (Nat.le_add_right κ 1).trans
      (Nat.le_mul_of_pos_left (κ + 1)
        (Nat.lt_of_lt_of_le (Nat.zero_lt_succ (κ * P.n κ))
          (Nat.le_add_right (κ * P.n κ + 1) (P.privLen κ))))
  · let x : ℝ := κ
    let m : ℝ := P.m κ
    have hx1 : 1 ≤ x := Nat.one_le_cast.mpr hκ1
    have hxpos : 0 < x := zero_lt_one.trans_le hx1
    have hx0 : 0 ≤ x := hxpos.le
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have hm1 : 1 ≤ m := ?_
    swap
    · have hn1 : 1 ≤ (P.n κ : ℝ) :=
        Nat.one_le_cast.mpr (hκ1.trans (P.le_n κ))
      have h := (P.G.hasStretch_iff τ).mp hs (P.n κ)
      rw [← P.m_eq] at h
      exact (Real.one_le_rpow hn1 (zero_le_one.trans hτ.le)).trans h
    have hmpos : 0 < m := zero_lt_one.trans_le hm1
    have hn : (Complexity.PolyExpr.pow .var (P.E * P.D)).eval κ = P.n κ := ?_
    swap
    · rw [Complexity.PolyExpr.eval_pow, Complexity.PolyExpr.eval_var,
        P.n_eq, P.ℓ_eq, pow_mul]
    have hmNat : P.m κ ≤ C * (κ + 1) ^ c := ?_
    swap
    · have heq : q.eval κ = P.G.outBound.eval (P.n κ) := ?_
      swap
      · dsimp only [q]
        rw [Complexity.PolyExpr.eval_subst, hn]
      have h := P.G.outLen_le (P.n κ)
      rw [← P.m_eq] at h
      exact (h.trans_eq heq.symm).trans (hq κ)
    have hmajor : m ≤ (C : ℝ) * (((κ + 1 : ℕ) : ℝ) ^ c) := ?_
    swap
    · dsimp only [m]
      exact_mod_cast hmNat
    have hκ2 : ((κ + 1 : ℕ) : ℝ) ≤ 2 * x := ?_
    swap
    · push_cast
      change x + 1 ≤ 2 * x
      linarith
    have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg (κ + 1)) hκ2 c) (Nat.cast_nonneg C)
    rw [mul_pow] at hp
    have hDmul := mul_le_mul_of_nonneg_right
      (le_max_right 1 ((C : ℝ) * (2 : ℝ) ^ c)) (pow_nonneg hx0 c)
    have hmupper : m ≤ D * x ^ c := ?_
    swap
    · dsimp only [D] at hDmul ⊢
      nlinarith
    have hmη : m ^ η ≤ D ^ η * x ^ ((c : ℝ) * η) := ?_
    swap
    · refine (Real.rpow_le_rpow hm0 hmupper hη.le).trans_eq ?_
      rw [Real.mul_rpow hD0 (pow_nonneg hx0 c),
        ← Real.rpow_natCast_mul hx0 c η]
    have hmp : m ^ τ' = m * m ^ η := ?_
    swap
    · change m ^ (1 + η) = m * m ^ η
      rw [Real.rpow_add hmpos, Real.rpow_one]
    have hsrel : (P.seedBitsAt κ : ℝ) ≤ m * x ^ (-ε) := hκs κ hκs'
    have hspow := Real.rpow_le_rpow (Nat.cast_nonneg (P.seedBitsAt κ)) hsrel
      (zero_le_one.trans hτ'.le)
    rw [Real.mul_rpow hm0 (Real.rpow_nonneg hx0 _),
      ← Real.rpow_mul hx0, hmp] at hspow
    have hηbound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmη hm0) (Real.rpow_nonneg hx0 ((-ε) * τ'))
    have hDstep : (m * (D ^ η * x ^ ((c : ℝ) * η))) * x ^ ((-ε) * τ') ≤
        (m * (x ^ (ε / 2) * x ^ ((c : ℝ) * η))) * x ^ ((-ε) * τ') := ?_
    swap
    · have hcoef := mul_le_mul_of_nonneg_right (hκD κ hκD')
        (Real.rpow_nonneg hx0 ((c : ℝ) * η))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoef hm0) (Real.rpow_nonneg hx0 ((-ε) * τ'))
    calc
      (P.seedBitsAt κ : ℝ) ^ τ' ≤
          (m * m ^ η) * x ^ ((-ε) * τ') := hspow
      _ ≤ (m * (D ^ η * x ^ ((c : ℝ) * η))) * x ^ ((-ε) * τ') := hηbound
      _ ≤ (m * (x ^ (ε / 2) * x ^ ((c : ℝ) * η))) * x ^ ((-ε) * τ') := hDstep
      _ = m * x ^ (ε / 2 + (c : ℝ) * η + (-ε) * τ') := ?_
      _ ≤ m * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hx1 hexp) hm0
      _ = m := mul_one _
    rw [Real.rpow_add hxpos (ε / 2 + (c : ℝ) * η) ((-ε) * τ'),
      Real.rpow_add hxpos (ε / 2) ((c : ℝ) * η)]
    ring

end TCSlib.Cryptography.Obfuscation.StructuredSeed
