/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.Sections
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Limits
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concave densities on a limiting affine graph

## Main definitions

No new definitions.

## Main results

* `tendsto_normalized_setIntegral_fst_of_section_root_tendsto`: convergence
  of midpoint-normalized section roots transfers continuous signed
  first-coordinate weights to limiting profile-weighted integrals.

* `tendsto_normalized_setIntegral_of_section_root_tendsto`: the same
  transfer for continuous signed ambient tests.

* `exists_concave_profile_of_iInter_eq_affine_graph`: positive signed
  integrals on shrinking bodies give nonnegative weighted graph integrals.

## References

* [LS93] László Lovász and Miklós Simonovits, *Random Walks in a Convex Body
  and an Improved Volume Algorithm*, Random Structures & Algorithms 4(4)
  (1993), 359–412, Lemma 2.5, proof of Claim 2, pp.380–381.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- Midpoint-normalized integrals of a continuous first-coordinate
weight over nested compact convex bodies converge to the corresponding
profile-weighted integral when their normalized section roots converge
along a subsequence and their intersection is an affine graph segment.
[LS93, Lemma 2.5, proof of Claim 2, pp.380–381]

The transverse dimension is positive. Positive body volumes imply
positive midpoint section volumes. The limit profile has no independent
measurability, concavity or boundedness hypothesis. Normalization uses
midpoint section volume, rather than body volume. The weight may have
either sign.

**Proof sketch.** The limiting graph puts the unit interval in every
first projection. Positive interior sections give positive midpoint
section volumes. All first projections lie in the compact initial
projection, so the homogeneous section bound uniformly bounds the
normalized section volumes. On the open unit interval, raising the
assumed root convergence to the dimension gives their convergence to
the profile's dimension power. Outside the closed interval, compact
nested-set containment makes each fixed section eventually empty.
Endpoints have zero measure. A continuous weight is bounded on the
compact initial projection. Dominated convergence, with a fixed compact
support, therefore gives convergence of the weighted section integrals.
The weighted section identity identifies these with the normalized
ambient integrals of the first-coordinate weight. -/
theorem tendsto_normalized_setIntegral_fst_of_section_root_tendsto
    {n : ℕ} (hn : 1 ≤ n)
    (K : ℕ → Set (ℝ × (Fin n → ℝ)))
    (hcompact : ∀ m : ℕ, IsCompact (K m))
    (hconvex : ∀ m : ℕ, Convex ℝ (K m))
    (hanti : Antitone K)
    (hvolume : ∀ m : ℕ, 0 < volume (K m))
    (b v : Fin n → ℝ)
    (hinter : (⋂ m : ℕ, K m) =
      Set.image (fun t : ℝ => (t, b + t • v)) (Set.Icc (0 : ℝ) 1))
    (φ : ℝ → ℝ) (u : ℕ → ℕ) (hu : StrictMono u)
    (hprofile : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      Filter.Tendsto
        (fun j : ℕ =>
          (volume.real {y : Fin n → ℝ | (t, y) ∈ K (u j)}) ^
              (1 / (n : ℝ)) /
            (volume.real
              {y : Fin n → ℝ | ((1 / 2 : ℝ), y) ∈ K (u j)}) ^
                (1 / (n : ℝ)))
        Filter.atTop (nhds (φ t)))
    (A : ℝ → ℝ) (hA : Continuous A) :
    Filter.Tendsto
      (fun j : ℕ =>
        (∫ p in K (u j), A p.1) /
          volume.real
            {y : Fin n → ℝ | ((1 / 2 : ℝ), y) ∈ K (u j)})
      Filter.atTop
      (nhds (∫ t in Set.Ioo (0 : ℝ) 1,
        (φ t) ^ n * A t)) :=
  (by
  -- Fix the normalization and bound every normalized section.
  let D (m : ℕ) := Set.image Prod.fst (K m)
  let w (m : ℕ) (t : ℝ) := volume.real {y : Fin n → ℝ | (t, y) ∈ K m}
  let c (m : ℕ) := w m (1 / 2)
  have hunit (m : ℕ) : Set.Icc (0 : ℝ) 1 ⊆ D m := by
    intro t ht
    have hp : (t, b + t • v) ∈ ⋂ m, K m := by
      rw [hinter]
      exact ⟨t, ht, rfl⟩
    exact ⟨(t, b + t • v), Set.mem_iInter.mp hp m, rfl⟩
  have hc (m : ℕ) : 0 < c m :=
    volumeReal_section_pos_of_mem_interior_projection hn (hcompact m) (hconvex m)
      (hvolume m) (interior_mono (hunit m) (by norm_num [interior_Icc]))
  have hD (m : ℕ) : D m ⊆ D 0 := Set.image_mono (hanti (Nat.zero_le m))
  obtain ⟨R₀, hR₀⟩ := (hcompact 0 |>.image continuous_fst).isBounded.exists_norm_le
  let R := max 1 R₀
  have hR : 1 ≤ R := le_max_left _ _
  have hproj (m : ℕ) : D m ⊆ Set.Icc (-R) R := by
    intro t ht
    have htR : |t| ≤ R := (hR₀ t (hD m ht)).trans (le_max_right _ _)
    exact abs_le.mp htR
  let C := (2 + 2 * R) ^ n
  have hC : 0 ≤ C := pow_nonneg (by linarith) _
  have hw (m : ℕ) (t : ℝ) : 0 ≤ w m t := measureReal_nonneg
  have hbound (m : ℕ) (t : ℝ) : w m t / c m ≤ C :=
    (div_le_iff₀ (hc m)).mpr
      (volumeReal_section_le_midpoint_mul_of_projection_subset hn
        (hcompact m) (hconvex m) (hunit m) hR (hproj m) t)
  have hzero (m : ℕ) {t : ℝ} (ht : t ∉ D m) : w m t = 0 := by
    have he : {y : Fin n → ℝ | (t, y) ∈ K m} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact ht ⟨(t, y), hy, rfl⟩
    change volume.real _ = 0
    rw [he, measureReal_empty]
  -- The normalized sections converge away from the two endpoints.
  have houtside (t : ℝ) (ht : t ∉ Set.Icc (0 : ℝ) 1) :
      ∀ᶠ j in Filter.atTop, w (u j) t / c (u j) = 0 := by
    obtain ⟨N, hN⟩ := exists_subset_nhds_of_isCompact' hanti.directed_ge hcompact
      (fun m => (hcompact m).isClosed) (by
        intro p hp
        apply ((isClosed_singleton (x := t)).preimage
          (continuous_fst : Continuous (Prod.fst : ℝ × (Fin n → ℝ) → ℝ))).isOpen_compl.mem_nhds
        change p.1 ≠ t
        rw [hinter] at hp
        obtain ⟨s, hs, rfl⟩ := hp
        intro he
        exact ht (he ▸ hs))
    filter_upwards [hu.tendsto_atTop.eventually (Filter.eventually_ge_atTop N)] with j hj
    rw [hzero (u j) (by
      rintro ⟨p, hp, hpt⟩
      exact hN (hanti hj hp) hpt), zero_div]
  have hinside (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      Filter.Tendsto (fun j => w (u j) t / c (u j)) Filter.atTop (nhds (φ t ^ n)) := by
    convert (hprofile t ht).pow n using 1
    funext j
    rw [div_pow, one_div,
      Real.rpow_inv_natCast_pow (hw (u j) t) (by omega),
      Real.rpow_inv_natCast_pow (hw (u j) (1 / 2)) (by omega)]

  -- A fixed compact support supplies the dominated-convergence bound.
  have hDcp : IsCompact (D 0) := (hcompact 0).image continuous_fst
  obtain ⟨B, hB⟩ := (hDcp.image hA).isBounded.exists_norm_le
  have hmeas (m : ℕ) : Measurable (w m) := by
    exact (measurable_measure_prodMk_left (ν := (volume : Measure (Fin n → ℝ)))
      (hcompact m).measurableSet).ennreal_toReal
  have hdom : Integrable ((D 0).indicator (fun _ : ℝ => C * B)) :=
    (integrableOn_const hDcp.measure_lt_top.ne).integrable_indicator hDcp.measurableSet
  have hnorm (j : ℕ) : ∀ᵐ t : ℝ, ‖w (u j) t / c (u j) * A t‖ ≤
      (D 0).indicator (fun _ => C * B) t := by
    filter_upwards [] with t
    by_cases ht : t ∈ D 0
    · rw [Set.indicator_of_mem ht, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hw _ _) (hc _).le)]
      exact mul_le_mul (hbound _ _) (hB (A t) ⟨t, ht, rfl⟩) (norm_nonneg _) hC
    · rw [hzero (u j) (fun h => ht (hD _ h)), zero_div, zero_mul, norm_zero,
        Set.indicator_of_notMem ht]
  have hlim : ∀ᵐ t : ℝ,
      Filter.Tendsto (fun j => w (u j) t / c (u j) * A t) Filter.atTop
        (nhds ((Set.Ioo (0 : ℝ) 1).indicator (fun t => φ t ^ n * A t) t)) := by
    filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume,
      (Set.countable_singleton (1 : ℝ)).ae_notMem volume] with t ht0 ht1
    change t ≠ 0 at ht0
    change t ≠ 1 at ht1
    by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht]
      exact (hinside t ht).mul_const _
    · rw [Set.indicator_of_notMem ht]
      have ht' : t ∉ Set.Icc (0 : ℝ) 1 := by
        intro ht'
        exact ht ⟨lt_of_le_of_ne ht'.1 (Ne.symm ht0), lt_of_le_of_ne ht'.2 ht1⟩
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [houtside t ht'] with j hj
      rw [hj, zero_mul]
  have hconv := tendsto_integral_of_dominated_convergence
    ((D 0).indicator (fun _ : ℝ => C * B))
    (fun j => (((hmeas (u j)).div_const _).mul hA.measurable).aestronglyMeasurable)
    hdom hnorm hlim

  -- Identify the scalar marginals with the body integrals.
  rw [integral_indicator measurableSet_Ioo] at hconv
  convert hconv using 1
  funext j
  rw [setIntegral_fst_eq_integral_volumeReal_section_mul (hcompact (u j)) hA.continuousOn,
    ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp [w, c]
  ring
)

/-- Along a subsequence on which midpoint-normalized section roots
converge at every interior parameter, midpoint-normalized integrals of
a continuous signed test over nested compact convex bodies converge
to the corresponding profile-weighted integral on their limiting
affine graph.
[LS93, Lemma 2.5, proof of Claim 2, pp.380–381]

The transverse dimension is positive. Positive body volumes ensure
positive midpoint section volumes. The limiting profile needs no
independent measurability, concavity or boundedness hypothesis.
Normalization is by midpoint section volume, rather than body volume.
This states the integral-transfer step separately from subsequence
selection and the eventual conclusion about signs of two tests.

**Proof sketch.** Apply normalized scalar section-integral transfer to
the continuous graph weight `t ↦ H(t, b + t • v)`. Apply it also to the
constant weight one to obtain convergence, and hence eventual
boundedness, of midpoint-normalized body masses. The ambient test
and its first-coordinate graph restriction agree on the limiting
intersection, so the uniform comparison theorem makes their difference
arbitrarily small on all sufficiently late bodies. Its normalized
integral is bounded by this uniform error times the normalized body
mass, and therefore tends to zero. Combining this error estimate with
scalar transfer gives the stated limit. -/
theorem tendsto_normalized_setIntegral_of_section_root_tendsto
    {n : ℕ} (hn : 1 ≤ n)
    (K : ℕ → Set (ℝ × (Fin n → ℝ)))
    (hcompact : ∀ m : ℕ, IsCompact (K m))
    (hconvex : ∀ m : ℕ, Convex ℝ (K m))
    (hanti : Antitone K)
    (hvolume : ∀ m : ℕ, 0 < volume (K m))
    (b v : Fin n → ℝ)
    (hinter : (⋂ m : ℕ, K m) =
      Set.image (fun t : ℝ => (t, b + t • v)) (Set.Icc (0 : ℝ) 1))
    (φ : ℝ → ℝ) (u : ℕ → ℕ) (hu : StrictMono u)
    (hprofile : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      Filter.Tendsto
        (fun j : ℕ =>
          (volume.real {y : Fin n → ℝ | (t, y) ∈ K (u j)}) ^
              (1 / (n : ℝ)) /
            (volume.real
              {y : Fin n → ℝ | ((1 / 2 : ℝ), y) ∈ K (u j)}) ^
                (1 / (n : ℝ)))
        Filter.atTop (nhds (φ t)))
    (H : (ℝ × (Fin n → ℝ)) → ℝ) (hH : Continuous H) :
    Filter.Tendsto
      (fun j : ℕ =>
        (∫ p in K (u j), H p) /
          volume.real
            {y : Fin n → ℝ | ((1 / 2 : ℝ), y) ∈ K (u j)})
      Filter.atTop
      (nhds (∫ t in Set.Ioo (0 : ℝ) 1,
        (φ t) ^ n * H (t, b + t • v))) :=
  (by
  let c (m : ℕ) := volume.real {y : Fin n → ℝ | ((1 / 2 : ℝ), y) ∈ K m}
  let A (t : ℝ) := H (t, b + t • v)
  have hA : Continuous A := hH.comp (continuous_id.prodMk
    (continuous_const.add (continuous_id.smul continuous_const)))
  let G (p : ℝ × (Fin n → ℝ)) := A p.1
  have hG : Continuous G := hA.comp continuous_fst
  have hgraph := tendsto_normalized_setIntegral_fst_of_section_root_tendsto
    hn K hcompact hconvex hanti hvolume b v hinter φ u hu hprofile A hA
  have hmass := tendsto_normalized_setIntegral_fst_of_section_root_tendsto
    hn K hcompact hconvex hanti hvolume b v hinter φ u hu hprofile (fun _ => 1) continuous_const
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hmass
  let M := |∫ t in Set.Ioo (0 : ℝ) 1, φ t ^ n| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hmass_bound : ∀ᶠ j in Filter.atTop, volume.real (K (u j)) / c (u j) < M :=
    hmass (Iio_mem_nhds (by dsimp [M]; linarith [le_abs_self (∫ t in Set.Ioo (0 : ℝ) 1, φ t ^ n)]))
  have heq : Set.EqOn H G (⋂ m, K m) := by
    intro p hp
    rw [hinter] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    rfl
  have herr : Filter.Tendsto
      (fun j => ((∫ p in K (u j), H p) - ∫ p in K (u j), G p) / c (u j))
      Filter.atTop (nhds (0 : ℝ)) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hη : 0 < ε / (2 * M) := div_pos hε (by positivity)
    obtain ⟨N, hN⟩ := eventually_abs_sub_lt_on_antitone_compacts K hanti
      (fun m => (hcompact m).isClosed) (hcompact 0) H G hH hG heq _ hη
    filter_upwards [hmass_bound,
      hu.tendsto_atTop.eventually (Filter.eventually_ge_atTop N)] with j hj hjN
    rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs, norm_div,
      Real.norm_eq_abs (c (u j)), abs_of_nonneg (show 0 ≤ c (u j) from measureReal_nonneg),
      ← integral_sub (hH.continuousOn.integrableOn_compact (hcompact (u j)))
        (hG.continuousOn.integrableOn_compact (hcompact (u j)))]
    calc
      ‖∫ p in K (u j), H p - G p‖ / c (u j) ≤
          (ε / (2 * M) * volume.real (K (u j))) / c (u j) :=
        div_le_div_of_nonneg_right
          (norm_setIntegral_le_of_norm_le_const (hcompact (u j)).measure_lt_top
            (fun p hp => by rw [Real.norm_eq_abs]; exact (hN _ hjN p hp).le))
          measureReal_nonneg
      _ = ε / (2 * M) * (volume.real (K (u j)) / c (u j)) := by ring
      _ ≤ ε / (2 * M) * M := mul_le_mul_of_nonneg_left hj.le hη.le
      _ < ε := by field_simp; nlinarith
  convert herr.add hgraph using 1
  · funext j
    dsimp [G, A, c]
    ring
  · simp only [zero_add]
    rfl
)

/-- Nested compact convex bodies shrinking to an affine graph segment,
with positive integrals of two continuous signed tests at every stage,
yield a nonzero concave profile giving nonnegative weighted integrals
of both tests along that segment.
[LS93, Lemma 2.5, proof of Claim 2, pp.380–381]

The dimension parameter counts the transverse coordinates. The affine
graph is written explicitly as `t ↦ b + t • v`. The profile is normalized
at the midpoint, is concave only on the open unit interval, and is not
asserted to have integral one. No endpoint convergence is required.

**Proof sketch.** A positive stage integral forces positive body volume.
The limiting graph places the unit interval inside every first
projection, so positive interior sections give positive midpoint
section volumes. Restrict each section-root profile to the unit
interval and divide by its positive midpoint value. The resulting
profiles are nonnegative and concave, with midpoint value one.
Midpoint-normalized subsequence selection supplies a concave interior
limit with midpoint value one and values between zero and two.
Apply normalized section-integral transfer to each of the two
continuous tests along that same subsequence. Each normalized stage
integral is positive, so both limiting weighted integrals are
nonnegative. -/
theorem exists_concave_profile_of_iInter_eq_affine_graph
    {n : ℕ} (hn : 1 ≤ n)
    (K : ℕ → Set (ℝ × (Fin n → ℝ)))
    (hcompact : ∀ m : ℕ, IsCompact (K m))
    (hconvex : ∀ m : ℕ, Convex ℝ (K m))
    (hanti : Antitone K) (b v : Fin n → ℝ)
    (hinter : (⋂ m : ℕ, K m) =
      Set.image (fun t : ℝ => (t, b + t • v)) (Set.Icc (0 : ℝ) 1))
    (F G : (ℝ × (Fin n → ℝ)) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hFpos : ∀ m : ℕ, 0 < ∫ p in K m, F p)
    (hGpos : ∀ m : ℕ, 0 < ∫ p in K m, G p) :
    ∃ φ : ℝ → ℝ,
      ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) φ ∧
      φ (1 / 2 : ℝ) = 1 ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, φ t ∈ Set.Icc (0 : ℝ) 2) ∧
      0 ≤ ∫ t in Set.Ioo (0 : ℝ) 1, (φ t) ^ n * F (t, b + t • v) ∧
      0 ≤ ∫ t in Set.Ioo (0 : ℝ) 1, (φ t) ^ n * G (t, b + t • v) :=
  (by
  have hvolume (m : ℕ) : 0 < volume (K m) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have h := hFpos m
    rw [setIntegral_measure_zero F hz] at h
    exact (lt_irrefl 0) h
  have hunit (m : ℕ) : Set.Icc (0 : ℝ) 1 ⊆ Set.image Prod.fst (K m) := by
    intro t ht
    have hp : (t, b + t • v) ∈ ⋂ m, K m := by
      rw [hinter]
      exact ⟨t, ht, rfl⟩
    exact ⟨(t, b + t • v), Set.mem_iInter.mp hp m, rfl⟩
  let c (m : ℕ) := volume.real {y : Fin n → ℝ | ((1 / 2 : ℝ), y) ∈ K m}
  have hc (m : ℕ) : 0 < c m :=
    volumeReal_section_pos_of_mem_interior_projection hn (hcompact m) (hconvex m)
      (hvolume m) (interior_mono (hunit m) (by norm_num [interior_Icc]))
  let ψ (m : ℕ) (t : ℝ) :=
    (volume.real {y : Fin n → ℝ | (t, y) ∈ K m}) ^ (1 / (n : ℝ)) /
      (c m) ^ (1 / (n : ℝ))
  have hroot (m : ℕ) : 0 < (c m) ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos (hc m) _
  have hψconcave (m : ℕ) : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (ψ m) := by
    have h := (concaveOn_rpow_volumeReal_section hn (hcompact m) (hconvex m)).subset
      (hunit m) (convex_Icc _ _)
    have hs := h.smul (inv_nonneg.mpr (hroot m).le)
    simpa only [smul_eq_mul, ψ, div_eq_mul_inv, mul_comm] using hs
  have hψnonneg (m : ℕ) (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ ψ m t :=
    div_nonneg (Real.rpow_nonneg measureReal_nonneg _) (hroot m).le
  have hψnorm (m : ℕ) : ψ m (1 / 2 : ℝ) = 1 :=
    div_self (ne_of_gt (hroot m))
  obtain ⟨φ, u, hu, hφconcave, hφnorm, hφbound, hprofile⟩ :=
    exists_subseq_tendsto_of_concaveOn_of_midpoint_eq_one ψ hψconcave hψnonneg hψnorm
  refine ⟨φ, hφconcave, hφnorm, hφbound, ?_, ?_⟩
  · have hlim := tendsto_normalized_setIntegral_of_section_root_tendsto
      hn K hcompact hconvex hanti hvolume b v hinter φ u hu hprofile F hF
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall
      (fun j => (div_pos (hFpos (u j)) (hc (u j))).le))
  · have hlim := tendsto_normalized_setIntegral_of_section_root_tendsto
      hn K hcompact hconvex hanti hvolume b v hinter φ u hu hprofile G hG
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall
      (fun j => (div_pos (hGpos (u j)) (hc (u j))).le))
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
