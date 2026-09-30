/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.AliceYFalse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Disjointness lower bound: headline theorems

The linear lower bound on the randomized communication complexity of set disjointness
[RY20, Thm 6.13]: every public-coin protocol computing `DISJ_n` with error at most `1/32`
communicates more than `⌊n / 2^32⌋` bits
(`floor_div_pow_lt_publicCoin_communicationComplexity_disjointness`). The result is due to
Kalyanasundaram–Schnitger [KS92] and Razborov [Raz92]; the information-complexity proof
formalised here follows Bar-Yossef–Jayram–Kumar–Sivakumar [BJKS04] as presented in
[RY20, Ch. 6].

## The proof across the twelve pieces

By Yao's minimax principle [RY20, Thm 3.3] it suffices to exhibit a distribution on inputs
under which every *deterministic* protocol of communication `ℓ < c · n` errs with
probability more than `1/32`. The distribution is Razborov's: a uniformly random special
coordinate `T`, independent uniform bits `(A_T, B_T)`, and at every other coordinate a
uniform pair from `{00, 01, 10}`; the inputs intersect with probability `1/4`, and only at
`T`. Its explicit sample space is `HardSample.lean`; the transcript variable
`Z = (S, Q)` with `Q = (T, A_<T, B_>T)` is `ZVariable.lean`. Write `𝒟` for the event that
the inputs are disjoint.

For a deterministic protocol `p` with transcript `S`, the argument bounds one quantity,
`claimInfo p = I(A_T : S | T A_<T B_≥T 𝒟) + I(B_T : S | T A_≤T B_>T 𝒟)`
(`InformationTerms.lean`), from both sides.

*Upper bound* [RY20, Ch. 6, eq. (6.3)] — `claimInfo p ≤ 2 ℓ · log 2 / n`. Under `𝒟` the
coordinate pairs are independent and `T` is uniform and independent of the inputs
(`DisjointModel.lean`, `HardDistributionEvents.lean`, `CoordinateVectorModel.lean`), so the
chain-rule inequality `Σ_i I(A_i : S | A_<i B_≥i) ≤ I(A : S | B)` [RY20, Lemma 6.15]
applies; averaging over `T` and bounding the right-hand side by the transcript entropy
`H(S) ≤ ℓ · log 2` gives the Alice term, and the Bob term follows by the Alice–Bob duality
(`DualHardSample.lean`, `DualityMeasurePreserving.lean`), which replaces the book's 'WLOG'.

*Lower bound* [RY20, Ch. 6, eq. (6.2)] — if `p` errs with probability at most `1/32` then
`claimInfo p > (1/32768)²`. Fixing `Z = z` restricts the inputs to a rectangle, so on
every `Z`-fiber the special pair `(A_T, B_T)` has a product law [RY20, Claim 6.14]
(`ZFiberMeasure.lean`, `RectangleSwitching.lean`). If `claimInfo p ≤ 2γ⁴/3`, the `Y_T = 0`
branch (`AliceYFalse.lean`) identifies `I(A_T : S | Q, B_T = 0)` with an average one-bit
divergence, Pinsker's inequality [RY20, Cor 6.7] turns it into an average total-variation
distance, and Markov's inequality shows that, on the `(A_T, B_T) = (0, 0)` slice, the
fibers where Alice's conditional special bit is more than `γ` from uniform have mass at
most `γ/2`; by duality the same holds for Bob. Hence the *good* fibers — those on which
the conditional law of `(A_T, B_T)` is within `2γ` of uniform — have mass at least
`(1 − 4γ)/4`. On a good fiber the protocol's answer is fixed while both `(0, 0)` and
`(1, 1)` occur with conditional probability at least `1/4 − 2γ`, so the protocol errs with
conditional probability at least `1/4 − 2γ`; averaging over good fibers gives
error `≥ (1/4)(1 − 4γ)(1/4 − 2γ)`, which exceeds `1/32` for `γ = 1/64`.

Combining the two bounds, a protocol with error `≤ 1/32` has
`(1/32768)² < 2 ℓ · log 2 / n`, i.e. `ℓ > (1/32768)² n / (2 log 2)`; the constant in the
statement is the slightly weaker `(1/32768)² / (3 log 2)`, and `2^{-32}` is a further
rounding of it. These constants, and the fixed error `1/32`, are formalisation artefacts: the
book states the bound as `Ω(e² n)` for error `1/2 − e` (via error reduction by repetition,
which is not formalised).

## Main definitions

None.

## Main results

* `two_thirds_mul_aliceInfoTermSpecialYFalse_le_aliceInfoTerm`: the `2/3` reweighting
  from `I(A_T : S | Q B_T 𝒟)` to `I(A_T : S | Q, B_T = 0)`.
* `integral_xDistance_sq_disjointSpecialYFalse_le_gamma_pow_four`: the Pinsker step.
* `measureReal_specialZeroZero_inter_xDistance_bad_le`,
  `measureReal_specialZeroZero_inter_yDistance_bad_le`,
  `one_div_four_mul_one_sub_four_mul_le_measureReal_goodZEvent`: most `(0, 0)`-fibers are
  good.
* `quarter_sub_two_mul_le_zFiberMeasure_protocolErrorEvent`,
  `goodZEvent_mul_quarter_sub_two_mul_le_distributionalError`: good fibers force error
  `1/4 − 2γ`.
* `one_div_32768_sq_lt_claimInfo_of_distributionalError_le`: error `≤ 1/32` forces
  `claimInfo > (1/32768)²`.
* `const_mul_n_le_complexity_of_distributionalError_le`: the distributional `Ω(n)` bound.
* `lt_publicCoin_communicationComplexity_disjointness_of_lt_const_mul_n`,
  `floor_div_pow_lt_publicCoin_communicationComplexity_disjointness`: the public-coin
  lower bound [RY20, Thm 6.13].

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Raz92] A. A. Razborov, "On the distributional complexity of disjointness",
  *Theoretical Computer Science* 106(2):385–390, 1992.
* [KS92] B. Kalyanasundaram, G. Schnitger, "The probabilistic communication complexity of
  set intersection", *SIAM J. Discrete Math.* 5(4):545–557, 1992.
* [BJKS04] Z. Bar-Yossef, T. S. Jayram, R. Kumar, D. Sivakumar, "An information statistics
  approach to data stream and communication complexity", *J. Comput. Syst. Sci.*
  68(4):702–732, 2004.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Functions.Disjointness

namespace RandomizedLowerBound

variable (n : ℕ+)

/-- Alice's information term on the `Y_T = 0` branch, weighted by the probability `2/3` of
that branch, is at most Alice's corrected information term:
`(2/3) · I(X_T : M | T, X_<T, Y_≥T, Y_T = 0, D) ≤ I(X_T : M | T, X_<T, Y_≥T, D)`
[RY20, Ch. 6, 'Since p(b_t = 0 | 𝒟) = 2/3, (6.3) implies 3ℓ/(2n) ≥ I(A_T : S | Q, B_T = 0)'].
The factor is `Pr[Y_T = false | D] = 2/3`, and the event `Y_T = false` is determined by the
conditioning variable because `Y_≥T` contains `Y_T`.

**Proof sketch.** Step 1: under the disjoint-conditioned law the event `Y_T = false` has
mass `2/3`. Step 2: that event is the preimage, under Alice's conditioning variable, of the
set of conditioning values with `Y_T = false`. Step 3: for an event determined by the
conditioning variable, its mass times the conditional information given the event is at
most the unconditional conditional information (the conditional information is a
nonnegative sum over conditioning values, and conditioning on the event keeps the summands
over its values); instantiate this with the mass `2/3`. -/
theorem two_thirds_mul_aliceInfoTermSpecialYFalse_le_aliceInfoTerm
    (p : ProtocolType n) :
    (2 / 3 : ℝ) * aliceInfoTermSpecialYFalse n p ≤ aliceInfoTerm n p := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointCondMeasure_isProbabilityMeasure n
  -- Step 1: the branch `Y_T = false` has mass `2/3` under `𝒟`.
  have hmass : μ.real Y0 = (2 / 3 : ℝ) := by
    simpa [μ, Y0] using disjointCondMeasure_measureReal_specialY_false n
  -- Step 2: the branch is determined by Alice's conditioning variable.
  have hdet : Y0 = (aliceClaimConditioning n) ⁻¹' aliceClaimConditioningYFalseValues n := by
    simpa [Y0] using specialY_false_eq_preimage_aliceClaimConditioningYFalseValues n
  -- Step 3: mass times conditional information on the branch is at most the information.
  have h :=
    ProbabilityTheory.measureReal_mul_cond_condMutualInfo_le_condMutualInfo_of_event_eq_preimage
      (μ := μ)
      (X := specialX n) (Y := message n p) (Z := aliceClaimConditioning n)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      (A := Y0) (B := aliceClaimConditioningYFalseValues n)
      MeasurableSet.of_discrete hdet
  simpa [μ, Y0, hmass, aliceInfoTermSpecialYFalse, aliceInfoTerm,
    disjointSpecialYFalseMeasure] using h

/-- The average, under `𝒟 ∧ Y_T = 0`, of Alice's one-bit fiber divergence is at most `3/2`
times Alice's corrected information term
[RY20, Ch. 6, 'Since p(b_t = 0 | 𝒟) = 2/3, (6.3) implies 3ℓ/(2n) ≥ I(A_T : S | Q, B_T = 0)']:
the average divergence is the `Y_T = 0` information term (`AliceYFalse.lean`), and the
`2/3` reweighting bounds that term by `(3/2)` times the corrected term. -/
theorem integral_xFiberKL_disjointSpecialYFalse_le_three_halves_mul_aliceInfoTerm
    (p : ProtocolType n) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
      (3 / 2 : ℝ) * aliceInfoTerm n p := by
  rw [integral_xFiberKL_disjointSpecialYFalse_eq_aliceInfoTermSpecialYFalse]
  have h := two_thirds_mul_aliceInfoTermSpecialYFalse_le_aliceInfoTerm n p
  nlinarith

/-- If the total corrected information `claimInfo` is at most `2γ⁴/3` for some `γ > 0`, then
the average, under `𝒟 ∧ Y_T = 0`, of Alice's one-bit fiber divergence is at most `2γ⁴`
[RY20, Ch. 6, Pinsker step '√(3ℓ ln 2 / 4n) ≥ E[α_{qs}]'] (with the parameter `γ` in place
of the explicit constant): combine the `3/2` bound with `aliceInfoTerm ≤ claimInfo`. -/
theorem integral_xFiberKL_disjointSpecialYFalse_le_two_mul_gamma_pow_four
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
      2 * γ ^ 4 := by
  have hkl :=
    integral_xFiberKL_disjointSpecialYFalse_le_three_halves_mul_aliceInfoTerm n p
  have hγ4_nonneg : 0 ≤ γ ^ 4 := by positivity
  linarith [aliceInfoTerm_le_claimInfo n p]

/-- If `claimInfo ≤ 2γ⁴/3` for some `γ > 0`, then the average, under `𝒟 ∧ Y_T = 0`, of the
squared total-variation distance between Alice's conditional special-bit law on the sample's
`Z`-fiber and the uniform bit is at most `γ⁴` [RY20, Ch. 6, Pinsker step
'√(3ℓ ln 2 / 4n) ≥ E[α_{qs}]'] (with the parameter `γ` in place of the explicit constant).
This is Pinsker's inequality `2 · tv² ≤ KL` on each fiber, averaged, combined with the
divergence bound `2γ⁴`. -/
theorem integral_xDistance_sq_disjointSpecialYFalse_le_gamma_pow_four
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    ∫ ω, (xDistance n p (zVariable n p ω)) ^ 2 ∂(disjointSpecialYFalseMeasure n) ≤
      γ ^ 4 := by
  have hpinsker :=
    two_mul_integral_xDistance_sq_le_integral_xFiberKL_disjointSpecialYFalse n p
  have hkl := integral_xFiberKL_disjointSpecialYFalse_le_two_mul_gamma_pow_four n p hγ hinfo
  nlinarith

open Classical in
/-- If `claimInfo ≤ 2γ⁴/3` for some `γ > 0`, then under the hard distribution the event
`(X_T, Y_T) = (0, 0)` intersected with the set of samples whose `Z`-fiber has Alice's
conditional special-bit law farther than `γ` (in total variation) from uniform has mass at
most `γ/2` [RY20, Ch. 6, eq. (6.2)] (most `(0, 0)`-fibers are good; deviation: the formal
proof uses a Markov/union bound with `γ` instead of RY's averaging argument, and the
`(0, 0)` slice is reached from the `Y_T = 0` branch by a factor `2`).

**Proof sketch.** Let `bad` be the set of samples whose fiber has Alice distance `> γ`.
Step 1: under `𝒟 ∧ Y_T = 0`, the squared distance has average at most `γ⁴`, hence (by
Jensen/Cauchy–Schwarz) the distance has average at most `γ²`. Step 2: by Markov's
inequality, `bad` has mass at most `γ²/γ = γ` under `𝒟 ∧ Y_T = 0`. Step 3: the law
conditioned on `(X_T, Y_T) = (0, 0)` is at most twice the law conditioned on
`𝒟 ∧ Y_T = 0` (the `(0, 0)` slice is half of the `Y_T = 0` branch), so `bad` has
conditional mass at most `2γ` given `(0, 0)`. Step 4: the event `(0, 0)` has mass `1/4`, so
unconditioning gives mass at most `(1/4) · 2γ = γ/2`. -/
theorem measureReal_specialZeroZero_inter_xDistance_bad_le
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    volume.real
      (specialZeroZero n ∩ {ω | γ < xDistance n p (zVariable n p ω)}) ≤ γ / 2 := by
  let μ : Measure (HardSample n) := volume
  let badX : Set (HardSample n) := {ω | γ < xDistance n p (zVariable n p ω)}
  -- Step 1: from `E[d²] ≤ γ⁴` to `E[d] ≤ γ²` under `𝒟 ∧ Y_T = 0`.
  have hsquared :=
    integral_xDistance_sq_disjointSpecialYFalse_le_gamma_pow_four n p hγ hinfo
  have havg :
      ∫ ω, xDistance n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
        γ ^ 2 :=
    disjointSpecialYFalseMeasure_integral_xDistance_le_of_integral_sq_le n p hsquared
  -- Step 2: Markov's inequality — the bad set has mass at most `γ` under `𝒟 ∧ Y_T = 0`.
  have hbad_y0 :
      (disjointSpecialYFalseMeasure n).real badX ≤ γ := by
    simpa [badX] using
      disjointSpecialYFalseMeasure_xDistance_bad_le_of_integral_le n p hγ havg
  -- Step 3: transfer to the `(0, 0)` slice, losing a factor `2`.
  have htransfer :
      (μ[|specialZeroZero n]).real badX ≤ 2 * γ := by
    have h :=
      volume_cond_specialZeroZero_measureReal_le_two_mul_disjointSpecialYFalseMeasure n badX
    have hbad_y0_two :
        2 * (disjointSpecialYFalseMeasure n).real badX ≤ 2 * γ := by
      nlinarith
    exact h.trans (by simpa [μ] using hbad_y0_two)
  -- Step 4: uncondition using `Pr[(X_T, Y_T) = (0, 0)] = 1/4`.
  have hcond_eq :
      (μ[|specialZeroZero n]).real badX =
        (μ.real (specialZeroZero n))⁻¹ * μ.real (specialZeroZero n ∩ badX) := by
    rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hA : μ.real (specialZeroZero n) = (1 / 4 : ℝ) := by
    simpa [μ, Measure.real] using measureReal_specialZeroZero n
  change μ.real (specialZeroZero n ∩ badX) ≤ γ / 2
  rw [hcond_eq, hA] at htransfer
  norm_num at htransfer
  linarith

open Classical in
/-- If `claimInfo ≤ 2γ⁴/3` for some `γ > 0`, then under the hard distribution the event
`(X_T, Y_T) = (0, 0)` intersected with the set of samples whose `Z`-fiber has Bob's
conditional special-bit law farther than `γ` from uniform has mass at most `γ/2`
[RY20, Ch. 6, eq. (6.2)] (most `(0, 0)`-fibers are good; deviation: Markov/union bound with
`γ` instead of RY's averaging argument). This is the Alice estimate applied to the dual
protocol, whose `claimInfo` is the same and whose Alice distance is the original Bob
distance. -/
theorem measureReal_specialZeroZero_inter_yDistance_bad_le
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    volume.real
      (specialZeroZero n ∩ {ω | γ < yDistance n p (zVariable n p ω)}) ≤ γ / 2 := by
  have hinfoDual : claimInfo n (dualProtocol n p) ≤ 2 * γ ^ 4 / 3 := by
    simpa [claimInfo_dualProtocol n p] using hinfo
  have h :=
    measureReal_specialZeroZero_inter_xDistance_bad_le n (dualProtocol n p) hγ hinfoDual
  simpa [volume_specialZeroZero_inter_xDistance_dualProtocol_eq_yDistance n p γ] using h

/-- If `claimInfo ≤ 2γ⁴/3` for some `γ > 0`, then the good event — the set of samples whose
`Z`-fiber has the conditional law of `(X_T, Y_T)` within `2γ` of uniform — has mass at least
`(1/4)(1 − 4γ)` under the hard distribution [RY20, Ch. 6, eq. (6.2)] (most `(0, 0)`-fibers
are good; deviation: the formal proof uses a Markov/union bound with `γ` instead of RY's
averaging argument, so the statement is a mass bound on good fibers rather than a bound on
`E[α_{qs}]`).

**Proof sketch.** Let `A` be the event `(X_T, Y_T) = (0, 0)`, of mass `1/4`, and let
`badX`, `badY` be the samples whose fiber has Alice, resp. Bob, distance `> γ`. Step 1:
`A ∩ badX` and `A ∩ badY` each have mass at most `γ/2`. Step 2: `A` is covered by
`good ∪ (A ∩ badX) ∪ (A ∩ badY)`, since a sample in `A` outside both bad sets has both
one-bit distances `≤ γ`, and on its fiber the pair law is a product, so the pair distance
is at most `2γ` (`mem_goodZEvent_of_xDistance_yDistance_le`). Step 3: by monotonicity and
subadditivity, `1/4 ≤ vol(good) + γ/2 + γ/2`, which rearranges to the claim. -/
theorem one_div_four_mul_one_sub_four_mul_le_measureReal_goodZEvent
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    (1 / 4 : ℝ) * (1 - 4 * γ) ≤
      volume.real (goodZEvent n p γ) := by
  let μ : Measure (HardSample n) := volume
  let A : Set (HardSample n) := specialZeroZero n
  let badX : Set (HardSample n) := {ω | γ < xDistance n p (zVariable n p ω)}
  let badY : Set (HardSample n) := {ω | γ < yDistance n p (zVariable n p ω)}
  -- Step 1: the two bad slices have mass at most `γ/2` each; `A` has mass `1/4`.
  have hxBad : μ.real (A ∩ badX) ≤ γ / 2 := by
    simpa [μ, A, badX] using measureReal_specialZeroZero_inter_xDistance_bad_le n p hγ hinfo
  have hyBad : μ.real (A ∩ badY) ≤ γ / 2 := by
    simpa [μ, A, badY] using measureReal_specialZeroZero_inter_yDistance_bad_le n p hγ hinfo
  have hA : μ.real A = (1 / 4 : ℝ) := by
    simpa [μ, A] using measureReal_specialZeroZero n
  -- Step 2: `A` is covered by the good event and the two bad slices.
  have hcover : A ⊆ goodZEvent n p γ ∪ (A ∩ badX) ∪ (A ∩ badY) := by
    intro ω hωA
    by_cases hx : γ < xDistance n p (zVariable n p ω)
    · exact Or.inl (Or.inr ⟨hωA, hx⟩)
    · by_cases hy : γ < yDistance n p (zVariable n p ω)
      · exact Or.inr ⟨hωA, hy⟩
      · have hxle : xDistance n p (zVariable n p ω) ≤ γ := le_of_not_gt hx
        have hyle : yDistance n p (zVariable n p ω) ≤ γ := le_of_not_gt hy
        exact Or.inl (Or.inl (mem_goodZEvent_of_xDistance_yDistance_le n p hxle hyle))
  -- Step 3: monotonicity and subadditivity of the measure, then rearrange.
  have hmono :
      μ.real A ≤ μ.real ((goodZEvent n p γ ∪ (A ∩ badX)) ∪ (A ∩ badY)) :=
    measureReal_mono hcover
  have hunion_outer :
      μ.real ((goodZEvent n p γ ∪ (A ∩ badX)) ∪ (A ∩ badY)) ≤
        μ.real (goodZEvent n p γ ∪ (A ∩ badX)) + μ.real (A ∩ badY) :=
    measureReal_union_le _ _
  have hunion_inner :
      μ.real (goodZEvent n p γ ∪ (A ∩ badX)) ≤
        μ.real (goodZEvent n p γ) + μ.real (A ∩ badX) :=
    measureReal_union_le _ _
  linarith

/-- Under the hard distribution conditioned on the fiber `Z = z`, intersecting an event with
that fiber does not change its mass. -/
theorem zFiberMeasure_inter_fiber
    (p : ProtocolType n)
    (z : ZType n p)
    (S : Set (HardSample n)) :
    (zFiberMeasure n p z).real ((zFiber n p z) ∩ S) =
      (zFiberMeasure n p z).real S := by
  rw [zFiberMeasure]
  rw [Measure.real]
  rw [ProbabilityTheory.cond_inter_self MeasurableSet.of_discrete]
  rfl

open Classical in
/-- On a good fiber `Z = z` (pair law within `2γ` of uniform), the conditional probability of
every value `b` of the special pair `(X_T, Y_T)` is within `2γ` of `1/4`
[RY20, Ch. 6, 'the conditional error given q, s is at least 1/4 − ν₁ − ν₂'] (the
disjointness probability is within `ν₁ + ν₂` of `1/4`; here `ν₁ + ν₂` is replaced by the
pair distance `≤ 2γ`). The proof is that a point mass differs from its uniform value by at
most the total-variation distance. -/
theorem abs_conditionalSpecialPairLaw_singleton_sub_quarter_le
    (p : ProtocolType n)
    {γ : ℝ}
    {z : ZType n p}
    (hgood : goodZ n p γ z)
    (b : Bool × Bool) :
    |(conditionalSpecialPairLaw n p z :
        Measure (Bool × Bool)).real {b} - (1 / 4 : ℝ)| ≤ 2 * γ := by
  have htv :=
    TVDistance.abs_measureReal_sub_le_tvDistance
      (conditionalSpecialPairLaw n p z) uniformBoolPair
      ⟨({b} : Set (Bool × Bool)), MeasurableSet.of_discrete⟩
  rw [uniformBoolPair_singleton] at htv
  have hgood' :
      tvDistance (conditionalSpecialPairLaw n p z) uniformBoolPair ≤ 2 * γ := by
    simpa [goodZ, zDistance] using hgood
  exact htv.trans hgood'

/-- On a good fiber `Z = z`, the conditional probability of every value `b` of the special
pair `(X_T, Y_T)` is at least `1/4 − 2γ` [RY20, Ch. 6, 'the conditional error given q, s
is at least 1/4 − ν₁ − ν₂']. -/
theorem quarter_sub_two_mul_le_conditionalSpecialPairLaw_singleton
    (p : ProtocolType n)
    {γ : ℝ}
    {z : ZType n p}
    (hgood : goodZ n p γ z)
    (b : Bool × Bool) :
    (1 / 4 : ℝ) - 2 * γ ≤
      (conditionalSpecialPairLaw n p z :
        Measure (Bool × Bool)).real {b} := by
  have h := abs_conditionalSpecialPairLaw_singleton_sub_quarter_le n p hgood b
  rw [abs_le] at h
  linarith

/-- On the fiber `Z = z`, every sample whose special pair `(X_T, Y_T)` equals `(o, o)`, where
`o` is the protocol's output on that fiber, is a sample on which the protocol errs
[RY20, Ch. 6, 'the conditional error given q, s is at least 1/4 − ν₁ − ν₂'] (the witnesses
of the error: if the protocol answers 'disjoint' the pair `(1, 1)` makes the inputs
intersect, and if it answers 'intersecting' the pair `(0, 0)` makes them disjoint).

**Proof sketch.** Step 1: on the fiber the protocol's run on the generated input returns
the fiber's output `o` (`run_eq_zOutput_of_zVariable_eq`). Step 2: if `o = false`, the
special bits are both `0`, so the generated inputs are disjoint (they can only intersect at
`T`), and the answer `false` is wrong for disjointness (which is `true` on disjoint inputs).
Step 3: if `o = true`, the special bits are both `1`, so the inputs intersect at `T`, and
the answer `true` is wrong. -/
theorem zFiber_inter_diag_specialPair_subset_protocolErrorEvent
    (p : ProtocolType n)
    {z : ZType n p} :
    (zFiber n p z) ∩ ((specialPair n) ⁻¹' {(zOutput n p z, zOutput n p z)}) ⊆
      protocolErrorEvent n p := by
  intro ω' hω'
  let b := zOutput n p z
  -- Step 1: on the fiber the protocol outputs the fiber's output `b`.
  have hrun' : p.run (X n ω') (Y n ω') = b := by
    simpa [b] using run_eq_zOutput_of_zVariable_eq n p (by simpa [zFiber] using hω'.1)
  have hpair : specialPair n ω' = (b, b) := by
    simpa [b] using hω'.2
  cases hb : b
  -- Step 2: output `false` with special pair `(0, 0)`: the inputs are disjoint, so this errs.
  · have hbits : ω'.xT = false ∧ ω'.yT = false := by
      simpa [specialPair, specialX, specialY, hb] using hpair
    have hdisj : Disjoint (X n ω') (Y n ω') := by
      rw [disjoint_X_Y_iff]
      intro hboth
      rw [hbits.1] at hboth
      simp at hboth
    simp [protocolErrorEvent, disjointness, hrun', hdisj, hb]
  -- Step 3: output `true` with special pair `(1, 1)`: the inputs intersect, so this errs.
  · have hbits : ω'.xT = true ∧ ω'.yT = true := by
      simpa [specialPair, specialX, specialY, hb] using hpair
    have hnot_disj : ¬Disjoint (X n ω') (Y n ω') := by
      rw [disjoint_X_Y_iff]
      exact not_not_intro hbits
    simp [protocolErrorEvent, disjointness, hrun', hnot_disj, hb]

/-- On a good fiber `Z = z`, the protocol errs with conditional probability at least
`1/4 − 2γ` [RY20, Ch. 6, 'the conditional error given q, s is at least 1/4 − ν₁ − ν₂'].
If the protocol output on the fiber is `true`, then the `(true, true)` special bit-pair
witnesses errors; otherwise `(false, false)` witnesses errors.

**Proof sketch.** Let `o` be the fiber's output. Step 1: the pair `(o, o)` has conditional
probability at least `1/4 − 2γ` on the good fiber. Step 2: the samples of the fiber with
special pair `(o, o)` are protocol errors, so by monotonicity their conditional mass is at
most the conditional error probability; intersecting with the fiber is invisible to the
fiber measure, and the conditional mass of the pair event is the pair law's point mass. -/
theorem quarter_sub_two_mul_le_zFiberMeasure_protocolErrorEvent
    (p : ProtocolType n)
    {γ : ℝ} {z : ZType n p}
    (hgood : goodZ n p γ z) :
    (1 / 4 : ℝ) - 2 * γ ≤
      (zFiberMeasure n p z).real (protocolErrorEvent n p) := by
  haveI : IsFiniteMeasure (zFiberMeasure n p z) := by
    rw [zFiberMeasure]
    infer_instance
  let b := zOutput n p z
  -- Step 1: the diagonal pair `(b, b)` has conditional mass at least `1/4 − 2γ`.
  have hmass :=
    quarter_sub_two_mul_le_conditionalSpecialPairLaw_singleton n p hgood (b, b)
  -- Step 2: that pair event is contained in the error event; compare masses.
  have hsubset :
      (zFiber n p z) ∩ ((specialPair n) ⁻¹' {(b, b)}) ⊆ protocolErrorEvent n p :=
    by simpa [b] using zFiber_inter_diag_specialPair_subset_protocolErrorEvent n p (z := z)
  have hmono :
      (zFiberMeasure n p z).real ((zFiber n p z) ∩ ((specialPair n) ⁻¹' {(b, b)})) ≤
        (zFiberMeasure n p z).real (protocolErrorEvent n p) :=
    measureReal_mono hsubset
  rw [zFiberMeasure_inter_fiber] at hmono
  rw [← conditionalSpecialPairLaw_singleton n p z (b, b)] at hmono
  exact hmass.trans hmono

/-- The mass of the good event times `1/4 − 2γ` is at most the probability, under the hard
distribution, that the protocol errs [RY20, Ch. 6, 'the conditional error given q, s is at
least 1/4 − ν₁ − ν₂'] (averaged over the good fibers). The proof decomposes both sides as
sums over `Z`-fibers and compares fiber by fiber: on a good fiber the conditional error is
at least `1/4 − 2γ`, and on a bad fiber the left summand is `0`. -/
theorem goodZEvent_mul_quarter_sub_two_mul_le_protocolErrorEvent
    (p : ProtocolType n)
    (γ : ℝ) :
    volume.real (goodZEvent n p γ) * ((1 / 4 : ℝ) - 2 * γ) ≤
      volume.real (protocolErrorEvent n p) := by
  rw [FiniteMeasureSpace.measureReal_eq_sum_cond_fiber_real
    (μ := volume) (Z := zVariable n p) (S := protocolErrorEvent n p)]
  unfold goodZEvent
  rw [FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z _
  by_cases hgood : goodZ n p γ z
  · simp only [hgood, ↓reduceIte]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact quarter_sub_two_mul_le_zFiberMeasure_protocolErrorEvent n p
      hgood
  · simp only [hgood, ↓reduceIte, one_div, zero_mul]
    positivity

/-- The mass of the good event times `1/4 − 2γ` is at most the distributional error of the
protocol for disjointness under the hard input distribution
[RY20, Ch. 6, 'the conditional error given q, s is at least 1/4 − ν₁ − ν₂']: the
distributional error is the mass of the sample-space error event. -/
theorem goodZEvent_mul_quarter_sub_two_mul_le_distributionalError
    (p : ProtocolType n) (γ : ℝ) :
    volume.real (goodZEvent n p γ) * ((1 / 4 : ℝ) - 2 * γ) ≤
      p.distributionalError (inputDist n) (disjointness n) := by
  rw [distributionalError_inputDist_eq_protocolErrorEvent]
  exact goodZEvent_mul_quarter_sub_two_mul_le_protocolErrorEvent n p γ

/-- A deterministic disjointness protocol whose distributional error under the hard
distribution is at most `1/32` has total corrected special-coordinate information
`claimInfo` strictly greater than `(1/32768)²` [RY20, Thm 6.13 proof] (the combination of
eqs. (6.2) and (6.3)). Deviation: explicit constants — error `≤ 1/32` forces
`claimInfo > (1/32768)²`, whereas RY conclude `E[α] ≥ 1/32`. The proof argues by
contradiction with `γ = 1/64`: if `claimInfo ≤ (1/32768)² ≤ 2γ⁴/3`, the good event has mass
at least `(1/4)(1 − 4γ) = 15/64` and the error is at least `(15/64)(1/4 − 2γ) = 210/4096`,
which exceeds `1/32`. -/
theorem one_div_32768_sq_lt_claimInfo_of_distributionalError_le
    (p : ProtocolType n)
    (herror : p.distributionalError (inputDist n) (disjointness n) ≤ 1 / 32) :
    (1 / 32768 : ℝ) ^ 2 < claimInfo n p := by
  by_contra hnot
  have hgood :=
    one_div_four_mul_one_sub_four_mul_le_measureReal_goodZEvent n p
      (γ := (1 / 64 : ℝ)) (by norm_num) (by linarith)
  have herror_lower :=
    goodZEvent_mul_quarter_sub_two_mul_le_distributionalError n p (1 / 64)
  linarith

/-- A deterministic disjointness protocol whose distributional error under the hard
distribution is at most `1/32` has communication at least `(1/32768)² · n / (3 log 2)`
[RY20, Thm 6.13] (the distributional form, before Yao's minimax). Deviation: explicit
constant `(1/32768)² · n / (3 log 2)` and natural-log units, in place of RY's `Ω(n)`. The
proof combines the lower bound `(1/32768)² < claimInfo` with the upper bound
`claimInfo ≤ 2 ℓ · log 2 / n` and clears denominators (the constant `3` rather than `2` is
slack absorbed by the final `nlinarith`). -/
theorem const_mul_n_le_complexity_of_distributionalError_le
    (p : ProtocolType n)
    (herror : p.distributionalError (inputDist n) (disjointness n) ≤ 1 / 32) :
    ((1 / 32768 : ℝ) ^ 2) * (n : ℝ) / (3 * Real.log 2) ≤ p.complexity := by
  have hinfo_lt := one_div_32768_sq_lt_claimInfo_of_distributionalError_le n p herror
  have hupper := claimInfo_le_average_info_upper n p
  have hmain :
      (1 / 32768 : ℝ) ^ 2 < 2 * (p.complexity * Real.log 2) / (n : ℝ) :=
    hinfo_lt.trans_le hupper
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hlog_pos : 0 < 3 * Real.log 2 := by positivity
  have hcomplexity_nonneg : 0 ≤ (p.complexity : ℝ) := by
    exact_mod_cast Nat.zero_le p.complexity
  rw [div_le_iff₀ hlog_pos]
  rw [lt_div_iff₀ hn_pos] at hmain
  nlinarith

/-- Every natural number `k` below `(1/32768)² · n / (3 log 2)` is strictly less than the
public-coin randomized communication complexity of disjointness on `n` elements at error
`1/32` [RY20, Thm 6.13] (via Yao's minimax principle [RY20, Thm 3.3]); historically
[KS92], [Raz92], [BJKS04]. Deviation: the fixed error `1/32` and the explicit constants
`2^{-32}` / `(1/32768)²/(3 log 2)` are formalisation artefacts, not RY's `Ω(e² n)`. The
proof applies the easy direction of minimax: any deterministic protocol of communication at
most `k` has distributional error more than `1/32` under the hard distribution, since
otherwise its communication would be at least the constant times `n`, which exceeds `k`. -/
theorem lt_publicCoin_communicationComplexity_disjointness_of_lt_const_mul_n
    {k : ℕ}
    (hk : (k : ℝ) <
      ((1 / 32768 : ℝ) ^ 2) * (n : ℝ) / (3 * Real.log 2)) :
    k < PublicCoin.communicationComplexity (disjointness n) (1 / 32 : ℝ) := by
  refine PublicCoin.lt_communicationComplexity_of_forall_distributionalError_gt
    (f := disjointness n) (ε := (1 / 32 : ℝ)) (n := k) (μ := inputDist n) ?_
  intro p hp
  by_contra hnot
  have herror : p.distributionalError (inputDist n) (disjointness n) ≤ 1 / 32 :=
    le_of_not_gt hnot
  have hlower := const_mul_n_le_complexity_of_distributionalError_le n p herror
  have hcomplexity_real : (p.complexity : ℝ) ≤ k := by
    exact_mod_cast hp
  linarith

/-- Headline theorem: the public-coin randomized communication complexity of disjointness on
`n` elements at error `1/32` is strictly greater than `⌊n / 2^32⌋`, so it is linear in `n`
[RY20, Thm 6.13] (via Yao's minimax principle [RY20, Thm 3.3]); historically [KS92],
[Raz92], [BJKS04]. Deviation: the fixed error `1/32` and the explicit constants `2^{-32}` /
`(1/32768)²/(3 log 2)` are formalisation artefacts, not RY's `Ω(e² n)` for error `1/2 − e`
(the error-reduction step of RY's proof is not formalised). The cutoff is the floor of the
real number `n / 2^32`, so the asymptotic constant is stated over the reals; the proof
checks `n / 2^32 < (1/32768)² n / (3 log 2)` using `log 2 < 1`. -/
theorem floor_div_pow_lt_publicCoin_communicationComplexity_disjointness
    : Nat.floor ((n : ℝ) / (2 ^ 32 : ℝ)) <
      PublicCoin.communicationComplexity (disjointness n) (1 / 32 : ℝ) := by
  apply lt_publicCoin_communicationComplexity_disjointness_of_lt_const_mul_n n
  have hlog_lt_one : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    linarith
  have hscaled :
      (n : ℝ) / (2 ^ 32 : ℝ) <
        ((1 / 32768 : ℝ) ^ 2) * (n : ℝ) / (3 * Real.log 2) := by
    field_simp
    linarith
  exact (Nat.floor_le (by positivity)).trans_lt hscaled

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
