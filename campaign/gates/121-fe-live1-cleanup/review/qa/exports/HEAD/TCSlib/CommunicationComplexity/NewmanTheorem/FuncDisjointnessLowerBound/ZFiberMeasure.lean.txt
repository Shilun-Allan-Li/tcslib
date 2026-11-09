/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.DualityMeasurePreserving
import TCSlib.CommunicationComplexity.NewmanTheorem.TVDistance
import TCSlib.CommunicationComplexity.NewmanTheorem.KLDivergence
import TCSlib.CommunicationComplexity.NewmanTheorem.Pinsker
import PFR.Kullback

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Disjointness lower bound: conditional laws on Z-fibers

The laws of the special-coordinate bits `(X_T, Y_T)` conditioned on a fibre of
`Z = (M, T, X_<T, Y_>T)` — the quantities `p(a_t b_t | q s)`, `p(a_t | q s)`, `p(b_t | q s)` of
[RY20, Claim 6.14] — together with their total-variation distances `α_{qs}`, `β_{qs}` from
the uniform bit. The file records how these conditional laws interact with the
disjoint-conditioned and `Y_T = 0`-conditioned measures, transports the Alice-side
quantities to the Bob side through duality, and proves the three analytic steps that turn
an information bound into a bound on the number of bad fibres: the one-bit Pinsker
inequality `2 α² ≤ KL`, Jensen's inequality `E[α] ≤ √(E[α²])`, and Markov's inequality.

## Main definitions

* `specialPair`: the bit pair `(X_T, Y_T)` at the special coordinate.
* `uniformBoolPair`: the uniform law on two bits.
* `zFiberMeasure`: the hard distribution conditioned on a `Z = z` fibre.
* `conditionalSpecialPairLaw`, `conditionalSpecialXLaw`, `conditionalSpecialYLaw`: the laws
  of `(X_T, Y_T)`, `X_T`, `Y_T` under `zFiberMeasure`.
* `zDistance`, `xDistance`, `yDistance`: their total-variation distances from uniform.
* `xFiberKL`: the KL divergence of Alice's conditional special-bit law from the uniform bit.

## Main results

* `disjointSpecialYFalseMeasure_specialX_law_eq_uniformBool`: under `𝒟 ∧ Y_T = 0`, Alice's
  special bit is uniform.
* `zFiberMeasure_real_apply`, `zFiberMeasure_cond_specialY_eq_volume_cond_inter`,
  `zFiberMeasure_cond_specialYFalse_eq_disjointSpecialYFalseMeasure_cond_zVariable`:
  conditional probabilities on fibres and the compatibility of the successive conditionings.
* `conditionalSpecialXLaw_dualProtocol_dualZValue`,
  `xDistance_dualProtocol_dualZValue_eq_yDistance`,
  `volume_specialZeroZero_inter_xDistance_dualProtocol_eq_yDistance`: Alice's one-bit law,
  distance and bad event for the dual protocol are Bob's for the original.
* `two_mul_xDistance_sq_le_xFiberKL`,
  `two_mul_integral_xDistance_sq_le_integral_xFiberKL_disjointSpecialYFalse`: the one-bit
  Pinsker inequality, pointwise and integrated.
* `disjointSpecialYFalseMeasure_integral_xDistance_le_of_integral_sq_le`,
  `disjointSpecialYFalseMeasure_xDistance_bad_le_of_integral_le`: the Jensen and Markov
  steps.

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

/-- The pair `(X_T, Y_T)` of Alice's and Bob's bits at the special coordinate of a sample.
Its conditional law on a `Z` fibre is `p(a_t b_t | q s)` in [RY20, Claim 6.14]. -/
def specialPair (ω : HardSample n) : Bool × Bool :=
  (specialX n ω, specialY n ω)

open Classical in
/-- Under the hard distribution conditioned on disjointness and on `Y_T = 0`, Alice's special
bit `X_T` is a uniform bit. This is the statement `p(a_t | q)` is uniform in
[RY20, Claim 6.14], specialised to the `Y_T = 0` conditioning used on the Alice side. -/
theorem disjointSpecialYFalseMeasure_specialX_law_eq_uniformBool :
    Measure.map (specialX n) (disjointSpecialYFalseMeasure n) =
      uniformBool := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  haveI : IsProbabilityMeasure (Measure.map (specialX n) (disjointSpecialYFalseMeasure n)) :=
    Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable (f := specialX n))
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro b
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real]
  rw [disjointSpecialYFalseMeasure_measureReal_specialX_singleton,
    uniformBool_singleton]

/-- The uniform law on one bit has full support. -/
theorem uniformBool_toPMF_ne_zero (b : Bool) :
    uniformBool.toPMF b ≠ 0 := by
  intro hb
  have hreal :
      (uniformBool.toPMF b).toReal =
        (1 / 2 : ℝ) := by
    simpa [Measure.toPMF_apply, Measure.real] using uniformBool_singleton b
  rw [hb] at hreal
  norm_num at hreal

/-- The uniform probability law on pairs of bits, giving mass `1/4` to each of the four
pairs; the reference law for `zDistance`. -/
noncomputable def uniformBoolPair : Measure (Bool × Bool) :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable instance uniformBoolPair_isProbabilityMeasure :
    IsProbabilityMeasure uniformBoolPair := by
  rw [uniformBoolPair]
  infer_instance

/-- Each bit-pair has mass `1 / 4` under the uniform law on two bits. -/
theorem uniformBoolPair_singleton (b : Bool × Bool) :
    uniformBoolPair.real {b} =
      (1 / 4 : ℝ) := by
  rw [uniformBoolPair]
  rw [Measure.real, ProbabilityTheory.uniformOn_univ]
  norm_num [Fintype.card_prod]

/-- The uniform law on two bits is the product of the one-bit uniform laws.

**Proof sketch.** Two measures on a finite type agree once they agree on singletons. The
left side gives every pair mass `1/4` (`uniformBoolPair_singleton`). On the right, write the
singleton `{(bx, bY)}` as the product set `{bx} ×ˢ {bY}`, so the product-measure formula gives
the product of the one-bit singleton masses, each `1/2` (`uniformBool_singleton`). -/
theorem uniformBoolPair_eq_prod :
    uniformBoolPair =
      uniformBool.prod uniformBool := by
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro b
  rw [uniformBoolPair_singleton]
  rcases b with ⟨bx, bY⟩
  change (1 / 4 : ℝ) =
    (uniformBool.prod uniformBool ({(bx, bY)})).toReal
  rw [show ({(bx, bY)} : Set (Bool × Bool)) = ({bx} : Set Bool) ×ˢ ({bY} : Set Bool) by
    ext p
    simp [Prod.ext_iff]]
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  have hx :
      (uniformBool ({bx} : Set Bool)).toReal =
        (1 / 2 : ℝ) := by
    simpa [Measure.real] using uniformBool_singleton bx
  have hy :
      (uniformBool ({bY} : Set Bool)).toReal =
        (1 / 2 : ℝ) := by
    simpa [Measure.real] using uniformBool_singleton bY
  rw [hx, hy]
  norm_num

/-- The hard distribution conditioned on the fibre `Z = z`: the law `p(· | q s)` of
[RY20, Claim 6.14] for the fixing `(q, s) = z`. It is a probability measure because every
achievable `Z` value has a nonempty fibre. -/
noncomputable def zFiberMeasure
    (p : ProtocolType n)
    (z : ZType n p) :
    Measure (HardSample n) :=
  volume[|zFiber n p z]

noncomputable instance zFiberMeasure_isProbabilityMeasure
    (p : ProtocolType n)
    (z : ZType n p) :
    IsProbabilityMeasure (zFiberMeasure n p z) := by
  rw [zFiberMeasure]
  exact ProbabilityTheory.cond_isProbabilityMeasure (volume_zFiber_ne_zero n p z)

/-- Conditional probabilities under a `Z=z` fiber are computed by intersecting with the fiber and
dividing by its mass. -/
theorem zFiberMeasure_real_apply
    (p : ProtocolType n)
    (z : ZType n p)
    (S : Set (HardSample n)) :
    (zFiberMeasure n p z).real S =
      (volume.real (zFiber n p z))⁻¹ *
        volume.real ((zFiber n p z) ∩ S) := by
  rw [zFiberMeasure]
  exact ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete _ S

open Classical in
/-- The mass of a `Z` fiber under the Alice-side conditioned measure, with the `3/2` scaling
from `Pr_D[Y_T=false]=2/3` made explicit. -/
theorem disjointSpecialYFalseMeasure_measureReal_zVariable
    (p : ProtocolType n)
    (z : ZType n p) :
    (disjointSpecialYFalseMeasure n).real (zFiber n p z) =
      (3 / 2 : ℝ) *
        (disjointCondMeasure n).real
          (((specialY n) ⁻¹' {false}) ∩ (zFiber n p z)) := by
  rw [disjointSpecialYFalseMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  rw [disjointCondMeasure_measureReal_specialY_false]
  ring

open Classical in
/-- Conditioning first on `Y_T=false` under `D`, then on a `Z` value, is the same as
conditioning under `D` on the intersection of those events. -/
theorem disjointSpecialYFalseMeasure_cond_zVariable_eq_cond_inter
    (p : ProtocolType n)
    (z : ZType n p) :
    (disjointSpecialYFalseMeasure n)[|zVariable n p ← z] =
      (disjointCondMeasure n)[|
        ((specialY n) ⁻¹' {false}) ∩ (zFiber n p z)] := by
  rw [disjointSpecialYFalseMeasure]
  exact ProbabilityTheory.cond_cond_eq_cond_inter
    MeasurableSet.of_discrete MeasurableSet.of_discrete (disjointCondMeasure n)

open Classical in
/-- Conditioning a `Z=z` fiber further on a special Bob-bit value is the same as conditioning the
ambient hard distribution on the intersection of those two fiber events. -/
theorem zFiberMeasure_cond_specialY_eq_volume_cond_inter
    (p : ProtocolType n)
    (z : ZType n p)
    (b : Bool) :
    (zFiberMeasure n p z)[|(specialY n) ⁻¹' {b}] =
      volume[|
        (zFiber n p z) ∩ ((specialY n) ⁻¹' {b})] := by
  rw [zFiberMeasure]
  exact ProbabilityTheory.cond_cond_eq_cond_inter
    MeasurableSet.of_discrete MeasurableSet.of_discrete volume

open Classical in
/-- Conditioning a `Z=z` fiber further on `Y_T=false` agrees with conditioning the
`D ∧ Y_T=false` measure on the same `Z` fiber. -/
theorem zFiberMeasure_cond_specialYFalse_eq_disjointSpecialYFalseMeasure_cond_zVariable
    (p : ProtocolType n)
    (z : ZType n p) :
    (zFiberMeasure n p z)[|(specialY n) ⁻¹' {false}] =
      (disjointSpecialYFalseMeasure n)[|zVariable n p ← z] := by
  rw [zFiberMeasure_cond_specialY_eq_volume_cond_inter]
  rw [show (zFiber n p z) ∩ ((specialY n) ⁻¹' {false}) =
      ((specialY n) ⁻¹' {false}) ∩ (zFiber n p z) by
    ext ω
    simp [and_comm]]
  rw [disjointSpecialYFalseMeasure_cond_zVariable_eq_cond_inter]
  rw [← volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent n
    (by
      intro ω hω
      exact mem_disjointEvent_of_specialY_eq_false n (by simpa using hω.1))]

open Classical in
/-- If the fibre `Z = z` has positive mass under the hard distribution conditioned on
disjointness and `Y_T = 0`, then the event `Y_T = 0` has positive probability under the
hard distribution conditioned on that fibre.

**Proof sketch.** The `𝒟 ∧ Y_T = 0` mass of the fibre is `3/2` times the
disjoint-conditioned mass of `{Y_T = 0} ∩ {Z = z}`, so the latter is nonzero. The
disjoint-conditioned law is absolutely continuous with respect to the uniform law, so the
uniform mass of that intersection is nonzero as well. Finally the conditional probability in
question is the product of the inverse (positive) fibre mass and the uniform mass of the
intersection, hence nonzero. -/
theorem zFiberMeasure_specialYFalse_ne_zero_of_disjointSpecialYFalseMeasure_ne_zero
    (p : ProtocolType n)
    (z : ZType n p)
    (hz : (disjointSpecialYFalseMeasure n).real (zFiber n p z) ≠ 0) :
    (zFiberMeasure n p z).real ((specialY n) ⁻¹' {false}) ≠ 0 := by
  let Z : Set (HardSample n) := zFiber n p z
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  -- Step 1: the disjoint-conditioned mass of `Y0 ∩ Z` is nonzero, by the `3/2` factorisation.
  have hfactor := disjointSpecialYFalseMeasure_measureReal_zVariable n p z
  have hμD_real_ne : (disjointCondMeasure n).real (Y0 ∩ Z) ≠ 0 := by
    intro hzero
    apply hz
    rw [hfactor]
    simp [Y0, Z, hzero]
  -- Step 2: absolute continuity transfers this to the uniform law.
  have hac_d : disjointCondMeasure n ≪ volume := by
    rw [disjointCondMeasure]
    exact ProbabilityTheory.cond_absolutelyContinuous
  have hμD_ne : (disjointCondMeasure n) (Y0 ∩ Z) ≠ 0 :=
    (MeasureTheory.measureReal_ne_zero_iff
      (μ := disjointCondMeasure n) (s := Y0 ∩ Z)).mp hμD_real_ne
  have hvol_inter_ne : volume (Y0 ∩ Z) ≠ 0 := by
    intro hvol
    exact hμD_ne (hac_d hvol)
  have hvol_inter_real_ne : volume.real (Z ∩ Y0) ≠ 0 := by
    rw [Set.inter_comm]
    exact (MeasureTheory.measureReal_ne_zero_iff
      (μ := volume) (s := Y0 ∩ Z)).mpr hvol_inter_ne
  -- Step 3: the fibre itself has positive uniform mass, so the conditional quotient is nonzero.
  have hzvol :
      volume Z ≠ 0 :=
    by simpa [Z] using volume_zFiber_ne_zero n p z
  have hzvol_real : volume.real Z ≠ 0 :=
    (MeasureTheory.measureReal_ne_zero_iff
      (μ := volume) (s := Z)).mpr hzvol
  rw [zFiberMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  change
    (volume.real Z)⁻¹ *
      volume.real (Z ∩ Y0) ≠ 0
  exact mul_ne_zero (inv_ne_zero hzvol_real) hvol_inter_real_ne

/-- The law of the special bit pair `(X_T, Y_T)` under the hard distribution conditioned on
the fibre `Z = z`: the distribution `p(a_t b_t | q s)` of [RY20, Claim 6.14]. -/
noncomputable def conditionalSpecialPairLaw
    (p : ProtocolType n)
    (z : ZType n p) : Measure (Bool × Bool) :=
  Measure.map (specialPair n) (zFiberMeasure n p z)

noncomputable instance conditionalSpecialPairLaw_isProbabilityMeasure
    (p : ProtocolType n)
    (z : ZType n p) :
    IsProbabilityMeasure (conditionalSpecialPairLaw n p z) := by
  rw [conditionalSpecialPairLaw]
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable (f := specialPair n))

/-- On a positive-mass `Z=z` fiber, the conditional `specialPair` singleton mass is the
corresponding preimage probability under the fiber measure. -/
theorem conditionalSpecialPairLaw_singleton
    (p : ProtocolType n)
    (z : ZType n p)
    (b : Bool × Bool) :
    Measure.real (conditionalSpecialPairLaw n p z) {b} =
      (zFiberMeasure n p z).real ((specialPair n) ⁻¹' {b}) := by
  rw [conditionalSpecialPairLaw]
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rfl

/-- The law of Alice's special bit `X_T` under the hard distribution conditioned on the fibre
`Z = z`: the distribution `p(a_t | q s)` of [RY20, Claim 6.14]. -/
noncomputable def conditionalSpecialXLaw
    (p : ProtocolType n)
    (z : ZType n p) : Measure Bool :=
  Measure.map (specialX n) (zFiberMeasure n p z)

noncomputable instance conditionalSpecialXLaw_isProbabilityMeasure
    (p : ProtocolType n)
    (z : ZType n p) :
    IsProbabilityMeasure (conditionalSpecialXLaw n p z) := by
  rw [conditionalSpecialXLaw]
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable (f := specialX n))

/-- The law of Bob's special bit `Y_T` under the hard distribution conditioned on the fibre
`Z = z`: the distribution `p(b_t | q s)` of [RY20, Claim 6.14]. -/
noncomputable def conditionalSpecialYLaw
    (p : ProtocolType n)
    (z : ZType n p) : Measure Bool :=
  Measure.map (specialY n) (zFiberMeasure n p z)

noncomputable instance conditionalSpecialYLaw_isProbabilityMeasure
    (p : ProtocolType n)
    (z : ZType n p) :
    IsProbabilityMeasure (conditionalSpecialYLaw n p z) := by
  rw [conditionalSpecialYLaw]
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable (f := specialY n))

/-- On a positive-mass `Z=z` fiber, Alice's conditional special-bit singleton mass is the
corresponding preimage probability under the fiber measure. -/
theorem conditionalSpecialXLaw_singleton
    (p : ProtocolType n)
    (z : ZType n p)
    (b : Bool) :
    Measure.real (conditionalSpecialXLaw n p z) {b} =
      (zFiberMeasure n p z).real ((specialX n) ⁻¹' {b}) := by
  rw [conditionalSpecialXLaw]
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rfl

/-- On a positive-mass `Z=z` fiber, Bob's conditional special-bit singleton mass is the
corresponding preimage probability under the fiber measure. -/
theorem conditionalSpecialYLaw_singleton
    (p : ProtocolType n)
    (z : ZType n p)
    (b : Bool) :
    Measure.real (conditionalSpecialYLaw n p z) {b} =
      (zFiberMeasure n p z).real ((specialY n) ⁻¹' {b}) := by
  rw [conditionalSpecialYLaw]
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rfl

/-- The total-variation distance between the law of `(X_T, Y_T)` conditioned on the fibre
`Z = z` and the uniform law on two bits. This is the quantity bounded by `ν₁ + ν₂` in
[RY20, Ch. 6, after Claim 6.14] ('the disjointness probability is within `ν₁ + ν₂` of
`1/4`'). -/
noncomputable def zDistance
    (p : ProtocolType n)
    (z : ZType n p) : ℝ :=
  tvDistance (conditionalSpecialPairLaw n p z) uniformBoolPair

/-- The total-variation distance between the law of Alice's special bit `X_T` conditioned on
the fibre `Z = z` and the uniform bit. This is `α_{qs} = |p(a_t | q s) − p(a_t | q)|` of
[RY20, Ch. 6, after Claim 6.14], since `p(a_t | q)` is uniform. -/
noncomputable def xDistance
    (p : ProtocolType n)
    (z : ZType n p) : ℝ :=
  tvDistance (conditionalSpecialXLaw n p z) uniformBool

/-- The total-variation distance between the law of Bob's special bit `Y_T` conditioned on
the fibre `Z = z` and the uniform bit. This is `β_{qs} = |p(b_t | q s) − p(b_t | q)|` of
[RY20, Ch. 6, after Claim 6.14], since `p(b_t | q)` is uniform. -/
noncomputable def yDistance
    (p : ProtocolType n)
    (z : ZType n p) : ℝ :=
  tvDistance (conditionalSpecialYLaw n p z) uniformBool

/-- Alice's one-bit conditional TV distance is nonnegative. -/
theorem xDistance_nonneg
    (p : ProtocolType n)
    (z : ZType n p) :
    0 ≤ xDistance n p z := by
  simp [xDistance, TVDistance.tvDistance_nonneg]

/-- Pulling a dual `Z` fiber intersected with a dual Alice-special-bit event back along
hard-sample duality gives the corresponding original Bob-special-bit event. -/
theorem dualHardSample_preimage_zVariable_dualZValue_inter_specialX
    (p : ProtocolType n)
    (z : ZType n p) (b : Bool) :
    (dualHardSample n) ⁻¹'
        ((zFiber n (dualProtocol n p) (dualZValue n p z)) ∩
          ((specialX n) ⁻¹' {b})) =
      (zFiber n p z) ∩ ((specialY n) ⁻¹' {b}) := by
  ext ω
  change
    zVariable n (dualProtocol n p) (dualHardSample n ω) = dualZValue n p z ∧
        specialX n (dualHardSample n ω) = b ↔
      zVariable n p ω = z ∧ specialY n ω = b
  rw [zVariable_dualProtocol_dualHardSample, specialX_dualHardSample]
  exact and_congr ((dualZValue_injective n p).eq_iff) Iff.rfl

/-- The ambient hard-sample measure gives corresponding original and dual one-bit `Z`-fiber
events the same mass. -/
theorem volume_zVariable_dualProtocol_dualZValue_inter_specialX
    (p : ProtocolType n)
    (z : ZType n p) (b : Bool) :
    volume
        ((zFiber n (dualProtocol n p) (dualZValue n p z)) ∩
          ((specialX n) ⁻¹' {b})) =
      volume
        ((zFiber n p z) ∩ ((specialY n) ⁻¹' {b})) := by
  let μ : Measure (HardSample n) := volume
  let S : Set (HardSample n) :=
    (zFiber n (dualProtocol n p) (dualZValue n p z)) ∩
      ((specialX n) ⁻¹' {b})
  have hpre :
      μ ((dualHardSample n) ⁻¹' S) = μ S :=
    Measure.measure_preimage_of_map_eq_self
      (volume_measurePreserving_dualHardSample n).map_eq
      MeasurableSet.of_discrete.nullMeasurableSet
  rw [← hpre]
  exact congrArg (fun S : Set (HardSample n) => μ S)
    (dualHardSample_preimage_zVariable_dualZValue_inter_specialX n p z b)

/-- The uniform hard-sample measure, as a real number, gives the event `Z' = z' ∧ X_T = b`
for the dual protocol and recoded value `z' = dualZValue z` the same mass as the event
`Z = z ∧ Y_T = b` for the original protocol. This is the real-valued form of
`volume_zVariable_dualProtocol_dualZValue_inter_specialX`. -/
theorem volume_measureReal_zVariable_dualProtocol_dualZValue_inter_specialX
    (p : ProtocolType n)
    (z : ZType n p) (b : Bool) :
    volume.real
        ((zFiber n (dualProtocol n p) (dualZValue n p z)) ∩
          ((specialX n) ⁻¹' {b})) =
      volume.real
        ((zFiber n p z) ∩ ((specialY n) ⁻¹' {b})) := by
  repeat rw [Measure.real]
  rw [volume_zVariable_dualProtocol_dualZValue_inter_specialX]

open Classical in
/-- The law of Alice's special bit for the dual protocol, conditioned on the recoded fibre
`Z' = dualZValue z`, equals the law of Bob's special bit for the original protocol conditioned
on `Z = z`. This is the duality that reduces the Bob-side case of the 'WLOG' step in
[RY20, Ch. 6, before eq. (6.2)] to the Alice-side case. -/
theorem conditionalSpecialXLaw_dualProtocol_dualZValue
    (p : ProtocolType n)
    (z : ZType n p) :
    conditionalSpecialXLaw n (dualProtocol n p) (dualZValue n p z) =
      conditionalSpecialYLaw n p z := by
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro b
  rw [conditionalSpecialXLaw_singleton, conditionalSpecialYLaw_singleton]
  rw [zFiberMeasure_real_apply, zFiberMeasure_real_apply]
  rw [volume_measureReal_zVariable_dualProtocol_dualZValue]
  rw [volume_measureReal_zVariable_dualProtocol_dualZValue_inter_specialX]

open Classical in
/-- Alice's one-bit distance `α` for the dual protocol at the recoded value `dualZValue z`
equals Bob's one-bit distance `β` for the original protocol at `z`. -/
theorem xDistance_dualProtocol_dualZValue_eq_yDistance
    (p : ProtocolType n)
    (z : ZType n p) :
    xDistance n (dualProtocol n p) (dualZValue n p z) = yDistance n p z := by
  simp [xDistance, yDistance, conditionalSpecialXLaw_dualProtocol_dualZValue n p z]

open Classical in
/-- For every threshold `γ`, the uniform probability that `(X_T, Y_T) = (0, 0)` and Alice's
distance `α` of the dual protocol at the sample's `Z` value exceeds `γ` equals the uniform
probability that `(X_T, Y_T) = (0, 0)` and Bob's distance `β` of the original protocol
exceeds `γ`. This transports the Alice-side Markov bound on bad fibres to the Bob side.

**Proof sketch.** The preimage of the dual bad event under sample duality is the original
bad event: duality fixes the event `(X_T, Y_T) = (0, 0)`, sends the `Z` value to its
recoding, and turns the dual `α` into the original `β`. Since duality preserves the uniform
law, the two events have the same mass. -/
theorem volume_specialZeroZero_inter_xDistance_dualProtocol_eq_yDistance
    (p : ProtocolType n)
    (γ : ℝ) :
    volume.real
        (specialZeroZero n ∩
          {ω | γ < xDistance n (dualProtocol n p) (zVariable n (dualProtocol n p) ω)}) =
      volume.real
        (specialZeroZero n ∩ {ω | γ < yDistance n p (zVariable n p ω)}) := by
  let μ : Measure (HardSample n) := volume
  let Sdual : Set (HardSample n) :=
    specialZeroZero n ∩
      {ω | γ < xDistance n (dualProtocol n p) (zVariable n (dualProtocol n p) ω)}
  let S : Set (HardSample n) :=
    specialZeroZero n ∩ {ω | γ < yDistance n p (zVariable n p ω)}
  -- Step 1: the preimage of the dual bad event under duality is the original bad event.
  have hpre : (dualHardSample n) ⁻¹' Sdual = S := by
    ext ω
    change
      dualHardSample n ω ∈ specialZeroZero n ∧
          γ < xDistance n (dualProtocol n p)
            (zVariable n (dualProtocol n p) (dualHardSample n ω)) ↔
        ω ∈ specialZeroZero n ∧ γ < yDistance n p (zVariable n p ω)
    rw [specialZeroZero_dualHardSample, zVariable_dualProtocol_dualHardSample,
      xDistance_dualProtocol_dualZValue_eq_yDistance]
  -- Step 2: duality preserves the uniform law, so the two events have equal mass.
  have hmeasure : μ S = μ Sdual := by
    have hpre_measure :
        μ ((dualHardSample n) ⁻¹' Sdual) = μ Sdual :=
      Measure.measure_preimage_of_map_eq_self
        (volume_measurePreserving_dualHardSample n).map_eq
        MeasurableSet.of_discrete.nullMeasurableSet
    simpa [hpre] using hpre_measure
  repeat rw [Measure.real]
  rw [hmeasure]

open Classical in
/-- Twice the square of Alice's one-bit distance `α` on the fibre `Z = z` is at most the KL
divergence of the conditional law of `X_T` from the uniform bit. This is Pinsker's
inequality [RY20, Lemma 6.6] applied to `p(a_t | q s)` against the uniform `p(a_t | q)`, the
form used in [RY20, Cor 6.7]. Deviation: the divergence is in nats, so the constant is `2`
rather than `2 / ln 2`; the divergence is finite because the uniform bit has full support. -/
theorem two_mul_xDistance_sq_le_toReal_klDiv_uniformBool
    (p : ProtocolType n)
    (z : ZType n p) :
    2 * xDistance n p z ^ 2 ≤
      (InformationTheory.klDiv
        (conditionalSpecialXLaw n p z)
        uniformBool).toReal := by
  rw [xDistance]
  exact two_mul_tvDistance_sq_le_toReal_klDiv
    (conditionalSpecialXLaw n p z) uniformBool
    (FiniteMeasureSpace.klDiv_ne_top_of_forall_toPMF_ne_zero
      (conditionalSpecialXLaw n p z) uniformBool uniformBool_toPMF_ne_zero)

/-- The KL divergence (in nats, as a real number) of the law of Alice's special bit
conditioned on the fibre `Z = z` from the uniform bit: the divergence
`D(p(a_t | q s) ‖ p(a_t | q))` whose average over `(q, s)` is the mutual information
`I(A_T : S | Q, B_T = 0)` in [RY20, Cor 6.7]. -/
noncomputable def xFiberKL
    (p : ProtocolType n)
    (z : ZType n p) : ℝ :=
  (InformationTheory.klDiv
    (conditionalSpecialXLaw n p z)
    uniformBool).toReal

/-- Twice the square of Alice's one-bit distance `α` on the fibre `Z = z` is at most the KL
cost `xFiberKL` of that fibre. This is Pinsker's inequality [RY20, Lemma 6.6] /
[RY20, Cor 6.7] for `p(a_t | q s)` against uniform, restated with `xFiberKL` (constant `2`
because the divergence is in nats). -/
theorem two_mul_xDistance_sq_le_xFiberKL
    (p : ProtocolType n)
    (z : ZType n p) :
    2 * xDistance n p z ^ 2 ≤ xFiberKL n p z := by
  simpa [xFiberKL] using two_mul_xDistance_sq_le_toReal_klDiv_uniformBool n p z

open Classical in
/-- Twice the average of `α²` over samples drawn from the hard distribution conditioned on
disjointness and `Y_T = 0` is at most the average of the fibre KL cost `xFiberKL` over the
same law. This is the averaged form of Pinsker's inequality [RY20, Lemma 6.6] used in
[RY20, Cor 6.7]; it follows from the pointwise bound by monotonicity of the integral
(constant `2` because the divergence is in nats). -/
theorem two_mul_integral_xDistance_sq_le_integral_xFiberKL_disjointSpecialYFalse
    (p : ProtocolType n) :
    2 * (∫ ω, (xDistance n p (zVariable n p ω)) ^ 2
        ∂(disjointSpecialYFalseMeasure n)) ≤
      ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  have hpoint :
      ∀ ω : HardSample n,
        2 * (xDistance n p (zVariable n p ω)) ^ 2 ≤
          xFiberKL n p (zVariable n p ω) := by
    intro ω
    exact two_mul_xDistance_sq_le_xFiberKL n p (zVariable n p ω)
  have h := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite hpoint
  simpa [μ, integral_const_mul] using h

open Classical in
/-- If the average of `α²` over the hard distribution conditioned on disjointness and
`Y_T = 0` is at most `γ⁴`, then the average of `α` over the same law is at most `γ²`. This is
the Jensen step `E[α] ≤ √(E[α²])` of [RY20, Cor 6.7], stated with the bound parametrised
as `γ⁴` so that the conclusion feeds Markov's inequality with threshold `γ`.

**Proof sketch.** Write `f = α ∘ Z`. Jensen's inequality for the convex function `x ↦ x²`
gives `(E f)² ≤ E[f²]`, hence `(E f)² ≤ γ⁴ = (γ²)²` by hypothesis. Since `E f ≥ 0` (the
distance is nonnegative) and `γ² ≥ 0`, taking square roots gives `E f ≤ γ²`. -/
theorem disjointSpecialYFalseMeasure_integral_xDistance_le_of_integral_sq_le
    (p : ProtocolType n)
    {γ : ℝ}
    (hsq :
      ∫ ω, (xDistance n p (zVariable n p ω)) ^ 2 ∂(disjointSpecialYFalseMeasure n) ≤
        γ ^ 4) :
    ∫ ω, xDistance n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
      γ ^ 2 := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  let f : HardSample n → ℝ := fun ω => xDistance n p (zVariable n p ω)
  -- Step 1: Jensen for `x ↦ x²` gives `(E f)² ≤ E[f²]`.
  have hjensen :
      (∫ ω, f ω ∂μ) ^ 2 ≤ ∫ ω, (f ω) ^ 2 ∂μ := by
    simpa using
      ConvexOn.map_integral_le
        (by simpa using (show ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) from
          Even.convexOn_pow (𝕜 := ℝ) (by decide : Even 2)))
        (by simpa using
          (show ContinuousOn (fun x : ℝ => x ^ 2) Set.univ from
            (continuous_pow 2).continuousOn))
        isClosed_univ
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
        (Integrable.of_finite (μ := μ))
        (Integrable.of_finite)
  -- Step 2: combine with the hypothesis `E[f²] ≤ γ⁴ = (γ²)²`.
  have hsq_bound :
      (∫ ω, f ω ∂μ) ^ 2 ≤ (γ ^ 2) ^ 2 := by
    calc
      (∫ ω, f ω ∂μ) ^ 2
          ≤ ∫ ω, (f ω) ^ 2 ∂μ := hjensen
      _ ≤ γ ^ 4 := by simpa [μ, f] using hsq
      _ = (γ ^ 2) ^ 2 := by ring
  -- Step 3: both sides are nonnegative, so take square roots.
  have hint_nonneg :
      0 ≤ ∫ ω, f ω ∂μ :=
    integral_nonneg fun ω => xDistance_nonneg n p (zVariable n p ω)
  have hγ_sq_nonneg : 0 ≤ γ ^ 2 := sq_nonneg γ
  exact (sq_le_sq₀ hint_nonneg hγ_sq_nonneg).mp hsq_bound

open Classical in
/-- If `γ > 0` and the average of `α` over the hard distribution conditioned on disjointness
and `Y_T = 0` is at most `γ²`, then under that law the probability that `α` exceeds `γ` is at
most `γ`. This is the Markov step: few fibres have large `α_{qs}`. (RY20 argues with the
expectation `E[α]` directly, [RY20, Ch. 6, eq. (6.2)]; Markov's inequality is used here to
extract a bound on bad fibres.)

**Proof sketch.** Write `f = α ∘ Z`. Markov's inequality for the nonnegative `f` gives
`γ · P(γ ≤ f) ≤ E f ≤ γ²`. The strict bad event `{γ < f}` is contained in `{γ ≤ f}`, and
dividing by `γ > 0` yields `P(γ ≤ f) ≤ γ`. -/
theorem disjointSpecialYFalseMeasure_xDistance_bad_le_of_integral_le
    (p : ProtocolType n)
    {γ : ℝ}
    (hγ : 0 < γ)
    (havg :
      ∫ ω, xDistance n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤ γ ^ 2) :
    (disjointSpecialYFalseMeasure n).real
      {ω | γ < xDistance n p (zVariable n p ω)} ≤ γ := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  let f : HardSample n → ℝ := fun ω => xDistance n p (zVariable n p ω)
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  -- Step 1: Markov's inequality `γ · P(γ ≤ f) ≤ E f`.
  have hmarkov :
      γ * μ.real {ω : HardSample n | γ ≤ f ω} ≤ ∫ ω, f ω ∂μ :=
    mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := f)
      (ae_of_all _ fun ω => xDistance_nonneg n p (zVariable n p ω))
      Integrable.of_finite γ
  -- Step 2: the strict bad event is contained in the non-strict one.
  have hbad_le :
      μ.real {ω : HardSample n | γ < f ω} ≤ μ.real {ω : HardSample n | γ ≤ f ω} :=
    measureReal_mono (by
      intro ω hω
      exact le_of_lt (by simpa using hω))
  -- Step 3: from `γ · P(γ ≤ f) ≤ γ²` and `γ > 0` conclude `P(γ ≤ f) ≤ γ`.
  have hge_le : μ.real {ω : HardSample n | γ ≤ f ω} ≤ γ := by
    have hge_mul :
        μ.real {ω : HardSample n | γ ≤ f ω} * γ ≤ γ ^ 2 := by
      calc
        μ.real {ω : HardSample n | γ ≤ f ω} * γ ≤ ∫ ω, f ω ∂μ := by
          simpa [mul_comm] using hmarkov
        _ ≤ γ ^ 2 := havg
    have hge_nonneg :
        0 ≤ μ.real {ω : HardSample n | γ ≤ f ω} :=
      measureReal_nonneg
    nlinarith
  exact hbad_le.trans hge_le

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
