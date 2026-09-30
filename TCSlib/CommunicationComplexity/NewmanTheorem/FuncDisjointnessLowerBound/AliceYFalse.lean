/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.InformationTerms

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Disjointness lower bound: the Y_T = 0 branch

The step of the proof of [RY20, Thm 6.13] that passes from the information term
`I(A_T : S | Q, B_T = 0)` to the averaged one-bit divergence
`E_{qs | b_t = 0} D(p(a_t | qs) ‖ p(a_t | q))` to which Pinsker's inequality is applied
[RY20, Cor 6.7]. Under the hard distribution conditioned on `𝒟 ∧ Y_T = 0`, Bob's special
bit is constant, so Alice's corrected conditioning `(T, X_<T, Y_≥T)` carries the same
information as the coarse conditioning `Q = (T, X_<T, Y_>T)`; and the reference law
`p(a_t | q, b_t = 0)` is uniform, because flipping Alice's special bit is a measure
preserving involution of every `Q`-fiber (`flipSpecialX`, the formal proof device for
'`p(a_t | q)` is uniform for every `q`' in [RY20, Claim 6.14]). Hence the average over
`Z = (S, Q)` of the divergence of Alice's conditional special-bit law from the uniform bit
equals `I(X_T : Z)`, and by the chain rule and the independence of `X_T` from `Q` this is
`I(X_T : S | Q, B_T = 0)`. The file also contains the explicit finite-sum forms of the
averaged divergence.

## Main definitions

* `aliceInfoTermSpecialYFalse`, `aliceCoarseInfoTermSpecialYFalse`: Alice's information term
  under `𝒟 ∧ Y_T = 0` with the fine conditioning `(T, X_<T, Y_≥T)` and with the coarse
  conditioning `(T, X_<T, Y_>T)`.
* `flipSpecialX`: the involution of the sample space toggling Alice's special bit.

## Main results

* `aliceInfoTermSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse`: the two conditionings
  give the same information term on the `Y_T = 0` branch.
* `volume_measurePreserving_flipSpecialX`,
  `disjointSpecialYFalseMeasure_measureReal_specialX_inter_coarseConditioning`,
  `mutualInfo_specialX_coarseConditioning_disjointSpecialYFalse_eq_zero`: Alice's special
  bit is uniform and independent of `Q` under `𝒟 ∧ Y_T = 0`.
* `integral_xFiberKL_disjointSpecialYFalse_eq_condKLDiv_zVariable`,
  `condKLDiv_specialX_zVariable_eq_mutualInfo_zVariable`,
  `mutualInfo_specialX_zVariable_eq_aliceCoarseInfoTermSpecialYFalse`: the averaged one-bit
  divergence is the mutual information `I(X_T : Z)`, which is the coarse information term.
* `integral_xFiberKL_disjointSpecialYFalse_eq_aliceInfoTermSpecialYFalse`: the averaged
  one-bit divergence equals Alice's `Y_T = 0` information term.

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

open Classical in
/-- On a sample with `Y_T = false`, Bob's padded suffix `Y_≥T` coincides with the padded
suffix `Y_>T`: the two differ only at the special coordinate, where both read `false`. -/
theorem yGeSpecial_eq_yAfterSpecial_of_specialY_false
    {ω : HardSample n} (hY : specialY n ω = false) :
    yGeSpecial n ω = yAfterSpecial n ω := by
  funext j
  by_cases hlt : ω.T < j
  · have hle : ω.T ≤ j := le_of_lt hlt
    simp [yGeSpecial, yAfterSpecial, hle, hlt]
  · by_cases hle : ω.T ≤ j
    · have hEq : j = ω.T := le_antisymm (not_lt.mp hlt) hle
      subst j
      simp only [yGeSpecial, le_refl, ↓reduceIte, yBit, yAfterSpecial, lt_self_iff_false]
      change ω.yT = false at hY
      exact hY
    · simp [yGeSpecial, yAfterSpecial, hle, hlt]

open Classical in
/-- On a sample with `Y_T = false`, Alice's corrected conditioning `(T, X_<T, Y_≥T)` equals
the coarse conditioning `Q = (T, X_<T, Y_>T)` that is part of `Z = (M, Q)`. -/
theorem aliceClaimConditioning_eq_coarseConditioning_of_specialY_false
    {ω : HardSample n} (hY : specialY n ω = false) :
    aliceClaimConditioning n ω = coarseConditioning n ω := by
  simp [aliceClaimConditioning, coarseConditioning,
    yGeSpecial_eq_yAfterSpecial_of_specialY_false n hY]

open Classical in
/-- Under the hard distribution conditioned on `𝒟 ∧ Y_T = false`, Bob's special bit is
almost surely `false`. -/
theorem disjointSpecialYFalseMeasure_ae_specialY_false :
    ∀ᵐ ω ∂disjointSpecialYFalseMeasure n, specialY n ω = false := by
  rw [disjointSpecialYFalseMeasure]
  filter_upwards [ae_cond_mem MeasurableSet.of_discrete] with ω hω
  simpa using hω

open Classical in
/-- Under the hard distribution conditioned on `𝒟 ∧ Y_T = false`, Alice's corrected
conditioning `(T, X_<T, Y_≥T)` is almost surely equal to the coarse conditioning
`Q = (T, X_<T, Y_>T)`. -/
theorem aliceClaimConditioning_ae_eq_coarseConditioning_disjointSpecialYFalse :
    aliceClaimConditioning n =ᵐ[disjointSpecialYFalseMeasure n] coarseConditioning n := by
  filter_upwards [disjointSpecialYFalseMeasure_ae_specialY_false n] with ω hY
  exact aliceClaimConditioning_eq_coarseConditioning_of_specialY_false n hY

open Classical in
/-- Alice's information term on the `Y_T = 0` branch: the conditional mutual information
`I(X_T : M | T, X_<T, Y_≥T, Y_T = 0, D)` between Alice's special bit and the transcript,
given Alice's corrected conditioning, under the hard distribution conditioned on
`𝒟 ∧ Y_T = 0` [RY20, Ch. 6, eq. (6.3) → 'I(A_T : S | Q, B_T = 0)'] (`B_T = 0` implies
`𝒟`, so conditioning on `𝒟` as well is harmless). -/
noncomputable def aliceInfoTermSpecialYFalse
    (p : ProtocolType n) : ℝ :=
  I[specialX n : message n p | aliceClaimConditioning n ; disjointSpecialYFalseMeasure n]

open Classical in
/-- Alice's information term on the `Y_T = 0` branch with the coarse conditioning: the
conditional mutual information `I(X_T : M | T, X_<T, Y_>T, Y_T = 0, D)` between Alice's
special bit and the transcript, given `Q = (T, X_<T, Y_>T)`, under the hard distribution
conditioned on `𝒟 ∧ Y_T = 0`; this is literally the quantity `I(A_T : S | Q, B_T = 0)` of
[RY20, Ch. 6, eq. (6.3) → 'I(A_T : S | Q, B_T = 0)'] (`B_T = 0` implies `𝒟`). -/
noncomputable def aliceCoarseInfoTermSpecialYFalse
    (p : ProtocolType n) : ℝ :=
  I[specialX n : message n p | coarseConditioning n ; disjointSpecialYFalseMeasure n]

open Classical in
/-- Under the hard distribution conditioned on `𝒟 ∧ Y_T = 0`, the average over `Z = (M, Q)`
of the divergence of the conditional law of Alice's special bit given `Z` from the uniform
bit law equals the mutual information `I(X_T : Z)`. This is the identity
`E_z D(p(x_t | z) ‖ p(x_t)) = I(X_T : Z)` behind [RY20, Cor 6.7], usable here because the
unconditional law of `X_T` under `𝒟 ∧ Y_T = 0` is uniform.

**Proof sketch.** Step 1: the law of `X_T` under `𝒟 ∧ Y_T = 0` is the uniform bit law, so
the divergence of that law from the uniform bit law is zero. Step 2: the general
decomposition `E_z D(p(x | z) ‖ q) = D(p(x) ‖ q) + I(X : Z)` (`condKLDiv_eq`, valid since
the uniform reference law has no zero atoms) then reduces to `I(X_T : Z)`, after rewriting
the mutual information as `H(X_T) − H(X_T | Z)`. -/
theorem condKLDiv_specialX_zVariable_eq_mutualInfo_zVariable
    (p : ProtocolType n) :
    condKLDiv (specialX n) id (zVariable n p) (disjointSpecialYFalseMeasure n)
        uniformBool =
      I[specialX n : zVariable n p ; disjointSpecialYFalseMeasure n] := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  -- Step 1: `X_T` is uniform under `𝒟 ∧ Y_T = 0`, so its divergence from uniform vanishes.
  have hmap : Measure.map (specialX n) (disjointSpecialYFalseMeasure n) =
      uniformBool := by
    exact disjointSpecialYFalseMeasure_specialX_law_eq_uniformBool n
  have hKL0 :
      KL[specialX n ; disjointSpecialYFalseMeasure n # id ;
        uniformBool] = 0 := by
    simp [KLDiv, hmap]
  -- Step 2: the decomposition of the conditional divergence into unconditional divergence
  -- plus mutual information.
  have hcond := condKLDiv_eq
    (μ := disjointSpecialYFalseMeasure n)
    (μ' := uniformBool)
    (X := specialX n) (Y := id) (Z := zVariable n p)
    Measurable.of_discrete Measurable.of_discrete
    (fun b hb => False.elim (uniformBool_toPMF_ne_zero b (by
      simpa [Measure.toPMF_apply] using hb)))
  rw [hKL0] at hcond
  rw [ProbabilityTheory.mutualInfo_eq_entropy_sub_condEntropy
    Measurable.of_discrete Measurable.of_discrete]
  simpa using hcond

open Classical in
/-- On the `Y_T = 0` branch, Alice's information term with the fine conditioning
`(T, X_<T, Y_≥T)` equals the one with the coarse conditioning `(T, X_<T, Y_>T)`:
`I(X_T : M | T, X_<T, Y_≥T, Y_T = 0, D) = I(X_T : M | Q, Y_T = 0, D)`
[RY20, Ch. 6, eq. (6.3) → 'I(A_T : S | Q, B_T = 0)'] (the book writes the term directly
with `Q`, since `B_T = 0` is fixed). The proof is that the two conditionings are almost
surely equal under the conditioned measure. -/
theorem aliceInfoTermSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse
    (p : ProtocolType n) :
    aliceInfoTermSpecialYFalse n p = aliceCoarseInfoTermSpecialYFalse n p := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  rw [aliceInfoTermSpecialYFalse, aliceCoarseInfoTermSpecialYFalse]
  exact ProbabilityTheory.condMutualInfo_congr_ae_finite
    (μ := disjointSpecialYFalseMeasure n)
    (X := specialX n) (Y := message n p) (Z := aliceClaimConditioning n)
    (X' := specialX n) (Y' := message n p) (Z' := coarseConditioning n)
    (by rfl) (by rfl) (aliceClaimConditioning_ae_eq_coarseConditioning_disjointSpecialYFalse n)

open Classical in
/-- The average, under `𝒟 ∧ Y_T = 0`, of Alice's one-bit fiber divergence `xFiberKL` at the
sample's `Z` value is the finite sum over `Z` values `z` of the mass of the fiber `Z = z`
times `xFiberKL z`. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable
    (p : ProtocolType n) :
    (∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n)) =
      ∑ z : ZType n p,
        (disjointSpecialYFalseMeasure n).real (zFiber n p z) *
          xFiberKL n p z := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  exact FiniteMeasureSpace.integral_comp_eq_sum_measureReal_fibers
    (μ := disjointSpecialYFalseMeasure n) (Z := zVariable n p) (f := xFiberKL n p)

open Classical in
/-- The average, under `𝒟 ∧ Y_T = 0`, of Alice's one-bit fiber divergence is the finite sum
over `Z` values `z` of the mass of `Z = z` times the divergence, from the uniform bit, of the
law of `X_T` under `𝒟 ∧ Y_T = 0` conditioned on `Z = z`. Fibers of zero mass contribute
nothing on either side; on positive-mass fibers `xFiberKL` is that divergence. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable_klDiv
    (p : ProtocolType n) :
    (∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n)) =
      ∑ z : ZType n p,
        (disjointSpecialYFalseMeasure n).real (zFiber n p z) *
          (InformationTheory.klDiv
            (Measure.map (specialX n)
              ((disjointSpecialYFalseMeasure n)[|zVariable n p ← z]))
            uniformBool).toReal := by
  rw [integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : (disjointSpecialYFalseMeasure n).real (zFiber n p z) = 0
  · simp [hz]
  · rw [xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv_of_ne_zero n p z hz]

open Classical in
/-- The average, under `𝒟 ∧ Y_T = 0`, of Alice's one-bit fiber divergence equals the
conditional divergence `E_z D(p(x_t | z) ‖ uniform)` of `X_T` given `Z`, in the form
`condKLDiv` of the entropy library. This is the averaged divergence
`E_{qs | b_t = 0} D(p(a_t | qs) ‖ p(a_t | q))` of [RY20, Cor 6.7] (mutual information as an
average divergence), with `p(a_t | q, b_t = 0)` uniform by [RY20, Claim 6.14]. The proof
matches the two finite sums fiber by fiber, converting the `ℝ≥0∞`-valued divergence on each
positive-mass fiber to the real-valued one. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_condKLDiv_zVariable
    (p : ProtocolType n) :
    (∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n)) =
      condKLDiv (specialX n) id (zVariable n p) (disjointSpecialYFalseMeasure n)
        uniformBool := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  rw [integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable_klDiv]
  rw [condKLDiv, tsum_fintype]
  apply Finset.sum_congr rfl
  intro z _
  dsimp [zFiber]
  by_cases hz :
      (disjointSpecialYFalseMeasure n).real ((zVariable n p) ⁻¹' {z}) = 0
  · simp [hz]
  · rw [ProbabilityTheory.toReal_klDiv_map_bool_eq_KLDiv_of_measureReal_ne_zero
      (μ := disjointSpecialYFalseMeasure n) (X := specialX n)
      (S := (zVariable n p) ⁻¹' {z}) uniformBool Measurable.of_discrete hz
      uniformBool_toPMF_ne_zero]

open Classical in
/-- The involution of the hard sample space that toggles Alice's special-coordinate bit
`X_T` and leaves the special coordinate `T`, Bob's special bit `Y_T` and all other
coordinates unchanged. It preserves the coarse conditioning `Q = (T, X_<T, Y_>T)`, the event
`Y_T = 0`, and the uniform measure, and is the formal device proving that `p(a_t | q)` is
uniform for every `q` [RY20, Claim 6.14] ('`p(a_t | q)` is uniform for every `q`'). -/
def flipSpecialX (ω : HardSample n) : HardSample n where
  T := ω.T
  xT := !ω.xT
  yT := ω.yT
  other := ω.other

/-- Flipping Alice's special bit twice returns the original sample: `flipSpecialX` is an
involution. -/
theorem flipSpecialX_flipSpecialX (ω : HardSample n) :
    flipSpecialX n (flipSpecialX n ω) = ω := by
  rcases ω with ⟨T, xT, yT, other⟩
  cases xT <;> rfl

/-- The preimage of a singleton `{ω}` under `flipSpecialX` is the singleton
`{flipSpecialX ω}`, since `flipSpecialX` is an involution. -/
theorem flipSpecialX_preimage_singleton (ω : HardSample n) :
    (flipSpecialX n) ⁻¹' ({ω}) = {flipSpecialX n ω} := by
  ext η
  constructor
  · intro hη
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hη
    rw [← hη]
    simp [flipSpecialX_flipSpecialX]
  · intro hη
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hη ⊢
    rw [hη, flipSpecialX_flipSpecialX]

/-- The singleton `{flipSpecialX ω}` has the same mass as `{ω}` under the uniform measure on
the hard sample space (every singleton has the same mass). -/
theorem volume_measureReal_singleton_flipSpecialX (ω : HardSample n) :
    volume.real ({flipSpecialX n ω} : Set (HardSample n)) =
      volume.real ({ω} : Set (HardSample n)) := by
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real
      ({flipSpecialX n ω} : Set (HardSample n))) =
    ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real
      ({ω} : Set (HardSample n)))
  repeat rw [Measure.real]
  rw [uniformOn_univ_measureReal_eq_card_subtype,
    uniformOn_univ_measureReal_eq_card_subtype]
  simp

/-- Flipping Alice's special bit is a measure preserving map of the hard sample space with
its uniform measure [RY20, Claim 6.14] ('`p(a_t | q)` is uniform for every `q`': the flip
exchanges the two values of `a_t` within every `q`-fiber). Since both measures are uniform
on a finite type, it suffices that singletons are sent to singletons of equal mass. -/
theorem volume_measurePreserving_flipSpecialX :
    MeasurePreserving (flipSpecialX n)
      volume volume := by
  refine ⟨Measurable.of_discrete, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro ω
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real, flipSpecialX_preimage_singleton,
    volume_measureReal_singleton_flipSpecialX]

/-- Alice's special bit of the flipped sample is the negation of the original special bit. -/
theorem specialX_flipSpecialX (ω : HardSample n) :
    specialX n (flipSpecialX n ω) = !specialX n ω := by
  simp [flipSpecialX, specialX]

/-- Bob's special bit is unchanged by `flipSpecialX`. -/
theorem specialY_flipSpecialX (ω : HardSample n) :
    specialY n (flipSpecialX n ω) = specialY n ω := by
  simp [flipSpecialX, specialY]

/-- Alice's padded prefix `X_<T` is unchanged by `flipSpecialX`: the flip only touches the
coordinate `T`, which the prefix does not read. -/
theorem xBeforeSpecial_flipSpecialX (ω : HardSample n) :
    xBeforeSpecial n (flipSpecialX n ω) = xBeforeSpecial n ω := by
  funext i
  by_cases hlt : i < ω.T
  · have hi : i ≠ ω.T := ne_of_lt hlt
    simp [xBeforeSpecial, xBit, flipSpecialX, hlt, hi]
  · simp [xBeforeSpecial, flipSpecialX, hlt]

/-- Bob's padded suffix `Y_>T` is unchanged by `flipSpecialX`. -/
theorem yAfterSpecial_flipSpecialX (ω : HardSample n) :
    yAfterSpecial n (flipSpecialX n ω) = yAfterSpecial n ω := by
  funext i
  simp [yAfterSpecial, yBit, flipSpecialX]

/-- The coarse conditioning `Q = (T, X_<T, Y_>T)` is unchanged by `flipSpecialX`, so the flip
maps every `Q`-fiber to itself. -/
theorem coarseConditioning_flipSpecialX (ω : HardSample n) :
    coarseConditioning n (flipSpecialX n ω) = coarseConditioning n ω := by
  unfold coarseConditioning
  rw [show specialCoordinate n (flipSpecialX n ω) = specialCoordinate n ω by
      simp [specialCoordinate, flipSpecialX],
    xBeforeSpecial_flipSpecialX, yAfterSpecial_flipSpecialX]

open Classical in
/-- Under the uniform (ambient) hard distribution, within the event `Y_T = false ∧ Q = c` for
any coarse conditioning value `c`, each value `b` of Alice's special bit `X_T` carries
exactly half of the mass of the event [RY20, Claim 6.14] ('`p(a_t | q)` is uniform for every
`q`', here in the ambient measure and on the `b_t = 0` slice; the flip argument is the
formal proof device).

**Proof sketch.** Let `E = {Y_T = false} ∩ {Q = c}`. Step 1: the two halves
`E ∩ {X_T = false}` and `E ∩ {X_T = true}` have equal mass, because `flipSpecialX` is
measure preserving, fixes `Y_T` and `Q`, and toggles `X_T`, so it maps one half onto the
other (its preimage of the `true` half is the `false` half). Step 2: `E` is the disjoint
union of the two halves, so its mass is the sum of theirs. Step 3: hence each half has mass
`(1/2) · vol(E)`; the two cases `b = false`, `b = true` are closed by linear arithmetic. -/
theorem volume_measureReal_specialYFalse_inter_coarseConditioning_inter_specialX
    (b : Bool) (c : Fin n × (Fin n → Bool) × (Fin n → Bool)) :
    volume.real
        (((specialY n) ⁻¹' {false}) ∩ ((coarseConditioning n) ⁻¹' {c}) ∩
          ((specialX n) ⁻¹' {b})) =
      (1 / 2 : ℝ) *
        volume.real
          (((specialY n) ⁻¹' {false}) ∩ ((coarseConditioning n) ⁻¹' {c})) := by
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  let C : Set (HardSample n) := (coarseConditioning n) ⁻¹' {c}
  let XF : Set (HardSample n) := (specialX n) ⁻¹' {false}
  let XT : Set (HardSample n) := (specialX n) ⁻¹' {true}
  -- Step 1: the flip carries the `X_T = false` half of the fiber onto the `X_T = true` half.
  have hfalse_true :
      volume.real (Y0 ∩ C ∩ XF) =
        volume.real (Y0 ∩ C ∩ XT) := by
    have hpre : (flipSpecialX n) ⁻¹' (Y0 ∩ C ∩ XT) = Y0 ∩ C ∩ XF := by
      ext ω
      simp [Y0, C, XF, XT, specialY_flipSpecialX, coarseConditioning_flipSpecialX,
        specialX_flipSpecialX]
    have hpre_measure :
        volume ((flipSpecialX n) ⁻¹' (Y0 ∩ C ∩ XT)) =
          volume (Y0 ∩ C ∩ XT) :=
      Measure.measure_preimage_of_map_eq_self
        (volume_measurePreserving_flipSpecialX n).map_eq
        MeasurableSet.of_discrete.nullMeasurableSet
    rw [← hpre]
    simpa [Measure.real] using congrArg ENNReal.toReal hpre_measure
  -- Step 2: the fiber is the disjoint union of its two halves, so its mass is the sum.
  have hunion : Y0 ∩ C = (Y0 ∩ C ∩ XF) ∪ (Y0 ∩ C ∩ XT) := by
    ext ω
    by_cases hx : specialX n ω = false
    · simp [Y0, C, XF, XT, hx]
    · have hxtrue : specialX n ω = true := by
        cases h : specialX n ω
        · exact False.elim (hx h)
        · rfl
      simp [Y0, C, XF, XT, hx]
  have hdisj : Disjoint (Y0 ∩ C ∩ XF) (Y0 ∩ C ∩ XT) := by
    rw [Set.disjoint_left]
    intro ω hF hT
    have hfalse : specialX n ω = false := by simpa [XF] using hF.2
    have htrue : specialX n ω = true := by simpa [XT] using hT.2
    rw [hfalse] at htrue
    simp at htrue
  have hsum :
      volume.real (Y0 ∩ C) =
        volume.real (Y0 ∩ C ∩ XF) +
          volume.real (Y0 ∩ C ∩ XT) := by
    simpa [← hunion] using
      (measureReal_union hdisj MeasurableSet.of_discrete :
        volume.real
            ((Y0 ∩ C ∩ XF) ∪ (Y0 ∩ C ∩ XT)) =
          volume.real (Y0 ∩ C ∩ XF) +
            volume.real (Y0 ∩ C ∩ XT))
  -- Step 3: each half is therefore half of the fiber, whichever value `b` takes.
  cases b
  · change volume.real (Y0 ∩ C ∩ XF) =
      (1 / 2 : ℝ) * volume.real (Y0 ∩ C)
    linarith
  · change volume.real (Y0 ∩ C ∩ XT) =
      (1 / 2 : ℝ) * volume.real (Y0 ∩ C)
    linarith

open Classical in
/-- Under the hard distribution conditioned on `𝒟 ∧ Y_T = 0`, the event
`X_T = b ∧ Q = c` has exactly half the mass of the event `Q = c`, for every bit `b` and every
coarse conditioning value `c`: Alice's special bit is uniform on every `Q`-fiber of the
conditioned law [RY20, Claim 6.14] ('`p(a_t | q)` is uniform for every `q`'; the flip
argument is the formal proof device, transported here from the ambient measure).

**Proof sketch.** Write `Y0 = {Y_T = false}`, `C = {Q = c}`, `Xb = {X_T = b}`, and `μ` for
the disjoint-conditioned law. Step 1: by the definition of conditioning, both sides are
`μ(Y0)⁻¹` times a `μ`-mass: `μ(Y0 ∩ Xb ∩ C)` on the left and `μ(Y0 ∩ C)` on the right.
Step 2: the ambient half-mass identity
`volume_measureReal_specialYFalse_inter_coarseConditioning_inter_specialX` gives
`vol(Y0 ∩ C ∩ Xb) = (1/2) vol(Y0 ∩ C)`. Step 3: both `Y0 ∩ C` and `Y0 ∩ C ∩ Xb` lie
inside the disjointness event (`Y_T = 0` forces disjointness), so their `μ`-masses are
their ambient masses divided by the mass of `𝒟`, and the half-mass identity transfers to
`μ`. Step 4: substitute and cancel the common factor `μ(Y0)⁻¹`. -/
theorem disjointSpecialYFalseMeasure_measureReal_specialX_inter_coarseConditioning
    (b : Bool) (c : Fin n × (Fin n → Bool) × (Fin n → Bool)) :
    (disjointSpecialYFalseMeasure n).real
        (((specialX n) ⁻¹' {b}) ∩ ((coarseConditioning n) ⁻¹' {c})) =
      (1 / 2 : ℝ) *
        (disjointSpecialYFalseMeasure n).real ((coarseConditioning n) ⁻¹' {c}) := by
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  let Xb : Set (HardSample n) := (specialX n) ⁻¹' {b}
  let C : Set (HardSample n) := (coarseConditioning n) ⁻¹' {c}
  -- Step 1: unfold the conditioning on `Y_T = false` on both sides.
  have hleft :
      (disjointSpecialYFalseMeasure n).real (Xb ∩ C) =
        ((disjointCondMeasure n).real Y0)⁻¹ *
          (disjointCondMeasure n).real (Y0 ∩ (Xb ∩ C)) := by
    rw [disjointSpecialYFalseMeasure]
    exact ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete _ (Xb ∩ C)
  have hright :
      (disjointSpecialYFalseMeasure n).real C =
        ((disjointCondMeasure n).real Y0)⁻¹ *
          (disjointCondMeasure n).real (Y0 ∩ C) := by
    rw [disjointSpecialYFalseMeasure]
    exact ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete _ C
  -- Step 2: the ambient half-mass identity on the `Y_T = false ∧ Q = c` fiber.
  have hbranch_volume :
      volume.real (Y0 ∩ C ∩ Xb) =
        (1 / 2 : ℝ) * volume.real (Y0 ∩ C) := by
    simpa [Y0, C, Xb, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      volume_measureReal_specialYFalse_inter_coarseConditioning_inter_specialX n b c
  -- Step 3: both events lie inside `𝒟`, so the identity transfers to the `𝒟`-conditioned law.
  have hbranch :
      (disjointCondMeasure n).real (Y0 ∩ C ∩ Xb) =
        (1 / 2 : ℝ) * (disjointCondMeasure n).real (Y0 ∩ C) := by
    rw [disjointCondMeasure]
    repeat rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
    have hY0C_subset_D : Y0 ∩ C ⊆ disjointEvent n := by
      intro ω hω
      exact mem_disjointEvent_of_specialY_eq_false n (by simpa [Y0] using hω.1)
    have hY0CX_subset_D : Y0 ∩ C ∩ Xb ⊆ disjointEvent n := by
      intro ω hω
      exact hY0C_subset_D ⟨hω.1.1, hω.1.2⟩
    rw [Set.inter_eq_right.mpr hY0CX_subset_D, Set.inter_eq_right.mpr hY0C_subset_D]
    rw [hbranch_volume]
    ring
  -- Step 4: substitute and cancel the common normalising factor.
  rw [hleft, hright]
  have hsets : Y0 ∩ (Xb ∩ C) = Y0 ∩ C ∩ Xb := by
    ext ω
    simp only [Set.mem_inter_iff]
    tauto
  rw [hsets, hbranch]
  ring

open Classical in
/-- Under the hard distribution conditioned on `𝒟 ∧ Y_T = 0`, Alice's special bit `X_T` is
independent of the coarse conditioning `Q = (T, X_<T, Y_>T)`: the mutual information
`I(X_T : Q)` vanishes. This is the sampling independence used before the transcript
rectangle is added, i.e. the uniformity of `p(a_t | q)` for every `q` behind the average
divergence of [RY20, Cor 6.7] (with `p(a_t | q, b_t = 0)` uniform by [RY20, Claim 6.14]).
The proof checks the product formula on singletons: the mass of `X_T = b ∧ Q = c` is half
the mass of `Q = c`, and the mass of `X_T = b` is `1/2`. -/
theorem mutualInfo_specialX_coarseConditioning_disjointSpecialYFalse_eq_zero :
    I[specialX n : coarseConditioning n ; disjointSpecialYFalseMeasure n] = 0 := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  apply (ProbabilityTheory.mutualInfo_eq_zero Measurable.of_discrete Measurable.of_discrete).mpr
  apply ProbabilityTheory.indepFun_of_measureReal_inter_preimage_singleton_eq_mul
    (μ := μ) (X := specialX n) (Y := coarseConditioning n)
    Measurable.of_discrete Measurable.of_discrete
  intro b c
  rw [show
      μ.real ((specialX n) ⁻¹' {b} ∩ (coarseConditioning n) ⁻¹' {c}) =
        (disjointSpecialYFalseMeasure n).real
          (((specialX n) ⁻¹' {b}) ∩ ((coarseConditioning n) ⁻¹' {c})) by rfl]
  rw [disjointSpecialYFalseMeasure_measureReal_specialX_inter_coarseConditioning]
  rw [disjointSpecialYFalseMeasure_measureReal_specialX_singleton]

open Classical in
/-- Under the hard distribution conditioned on `𝒟 ∧ Y_T = 0`, the mutual information
`I(X_T : Z)` between Alice's special bit and the full variable `Z = (M, Q)` equals the
coarse information term `I(X_T : M | Q, Y_T = 0, D)`; the chain rule
`I(X_T : Z) = I(X_T : Q) + I(X_T : M | Q)` together with `I(X_T : Q) = 0`. This is the
passage from the average divergence `E_{qs} D(p(a_t | qs) ‖ p(a_t | q))` of [RY20, Cor 6.7]
to the conditional information `I(A_T : S | Q, B_T = 0)`.

**Proof sketch.** Step 1: `Z` is an injective recoding of the pair `(Q, M)` (the record
`Z` is determined by, and determines, its coarse part and its transcript), so
`I(X_T : Z) = I(X_T : (Q, M))`. Step 2: by the chain rule for mutual information,
`I(X_T : (Q, M)) = I(X_T : Q) + I(X_T : M | Q)`. Step 3: the first summand vanishes by
`mutualInfo_specialX_coarseConditioning_disjointSpecialYFalse_eq_zero`, and the second is
the coarse information term by definition. -/
theorem mutualInfo_specialX_zVariable_eq_aliceCoarseInfoTermSpecialYFalse
    (p : ProtocolType n) :
    I[specialX n : zVariable n p ; disjointSpecialYFalseMeasure n] =
      aliceCoarseInfoTermSpecialYFalse n p := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  -- Step 1: `Z` is an injective recoding of the pair `(Q, M)`.
  let swappedZ :
      HardSample n → (Fin n × (Fin n → Bool) × (Fin n → Bool)) × TranscriptType n p :=
    fun ω => (coarseConditioning n ω, message n p ω)
  let swapZ :
      ZType n p →
        (Fin n × (Fin n → Bool) × (Fin n → Bool)) × TranscriptType n p :=
    fun z => ((z.specialCoordinate, z.xBefore, z.yAfter), z.transcript)
  have hswap_fun : swappedZ = swapZ ∘ zVariable n p := by
    funext ω
    simp [swappedZ, swapZ, zVariable, rawZVariable, message, coarseConditioning,
      ZType.specialCoordinate, ZType.xBefore, ZType.yAfter, ZType.transcript]
  have hrec :
      I[specialX n : swappedZ ; μ] =
        I[specialX n : zVariable n p ; μ] := by
    rw [hswap_fun]
    exact ProbabilityTheory.mutualInfo_comp_right_of_injective
      (μ := μ) (X := specialX n) (Y := zVariable n p)
      Measurable.of_discrete Measurable.of_discrete
      swapZ Measurable.of_discrete
      (by
        intro z z' h
        have h' := Prod.ext_iff.mp h
        apply ZType.ext
        · exact h'.2
        · exact congrArg Prod.fst h'.1
        · exact congrArg (fun c => c.2.1) h'.1
        · exact congrArg (fun c => c.2.2) h'.1)
  -- Step 2: chain rule `I(X_T : (Q, M)) = I(X_T : Q) + I(X_T : M | Q)`.
  have hchain :
      I[specialX n : swappedZ ; μ] =
        I[specialX n : coarseConditioning n ; μ] +
          I[specialX n : message n p | coarseConditioning n ; μ] := by
    simpa [swappedZ, μ] using
      ProbabilityTheory.mutualInfo_prod_right_eq_add
        (μ := disjointSpecialYFalseMeasure n)
        (X := specialX n) (Y := coarseConditioning n) (W := message n p)
        Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
  -- Step 3: `I(X_T : Q) = 0`, and the remaining term is the coarse information term.
  calc
    I[specialX n : zVariable n p ; disjointSpecialYFalseMeasure n]
        = I[specialX n : swappedZ ; μ] := by
          simpa [μ] using hrec.symm
    _ = I[specialX n : coarseConditioning n ; μ] +
          I[specialX n : message n p | coarseConditioning n ; μ] := hchain
    _ = aliceCoarseInfoTermSpecialYFalse n p := by
          rw [mutualInfo_specialX_coarseConditioning_disjointSpecialYFalse_eq_zero]
          simp [aliceCoarseInfoTermSpecialYFalse, μ]

open Classical in
/-- The average, under `𝒟 ∧ Y_T = 0`, of Alice's one-bit fiber divergence at the sample's `Z`
value equals the coarse information term `I(X_T : M | T, X_<T, Y_>T, Y_T = 0, D)`: the
average divergence is `I(X_T : Z)`, which is the coarse term. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse
    (p : ProtocolType n) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) =
      aliceCoarseInfoTermSpecialYFalse n p := by
  rw [integral_xFiberKL_disjointSpecialYFalse_eq_condKLDiv_zVariable]
  rw [condKLDiv_specialX_zVariable_eq_mutualInfo_zVariable]
  exact mutualInfo_specialX_zVariable_eq_aliceCoarseInfoTermSpecialYFalse n p

open Classical in
/-- The average, under `𝒟 ∧ Y_T = 0`, of Alice's one-bit fiber divergence at the sample's `Z`
value equals Alice's `Y_T = 0` information term
`I(X_T : M | T, X_<T, Y_≥T, Y_T = 0, D)`. This is the identity
`I(A_T : S | Q, B_T = 0) = E_{qs | b_t = 0} D(p(a_t | qs, b_t = 0) ‖ p(a_t | q, b_t = 0))`
of [RY20, Cor 6.7] (mutual information as an average divergence), with the reference law
`p(a_t | q, b_t = 0)` uniform by [RY20, Claim 6.14]. The proof composes the
coarse-conditioning identity (mutual information `I(X_T : Z)` as average divergence) with the
equality of the fine and coarse information terms on the `Y_T = 0` branch. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_aliceInfoTermSpecialYFalse
    (p : ProtocolType n) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) =
      aliceInfoTermSpecialYFalse n p := by
  rw [aliceInfoTermSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse]
  exact integral_xFiberKL_disjointSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse n p

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
