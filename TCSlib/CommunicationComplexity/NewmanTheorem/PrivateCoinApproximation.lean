/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinBasic
import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinFiniteMessage
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.ENNReal.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coin Approximation

## Main results

- `PrivateCoin.Internal.uniformApprox_approx`: CDF-inversion construction for approximating arbitrary PMFs by uniform distributions over CoinTape randomness

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

open MeasureTheory
open scoped ENNReal

namespace CommunicationComplexity

namespace Internal

def cdf {m : ℕ} (p : PMF (Fin m)) (n : ℕ) : ℝ≥0∞ :=
  ∑ j : Fin m, if j < n then p j else 0

@[simp] lemma cdf_zero {m : ℕ} (p : PMF (Fin m)) :
    cdf p 0 = 0 := by
  simp [cdf]

lemma cdf_succ {m : ℕ} (p : PMF (Fin m)) (n : Fin m) :
    cdf p (n + 1) = cdf p n + p n := by
  simp only [cdf]
  -- Split: ∑ (if j < n+1 ...) = ∑ (if j < n ...) + ∑ (if j = n ...)
  have key : ∀ j : Fin m,
      (if (j : ℕ) < (n : ℕ) + 1 then (p j : ℝ≥0∞) else 0) =
      (if (j : ℕ) < (n : ℕ) then p j else 0) +
      (if j = n then p n else 0) := by
    intro j
    split_ifs with h1 h2 <;> simp_all <;> omega
  simp_rw [key, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

lemma cdf_one {m : ℕ} (p : PMF (Fin m)) :
    cdf p m = 1 := by
  simp only [cdf, Fin.is_lt, ↓reduceIte]
  have hsum := PMF.tsum_coe p
  simp only [tsum_fintype] at hsum
  exact hsum

lemma cdf_mono {m : ℕ} (p : PMF (Fin m)) :
    Monotone (cdf p) := by
  intro i j hij
  unfold cdf
  apply Finset.sum_le_sum
  intro k _
  split_ifs with h1 h2
  · exact le_refl _
  · exact absurd (lt_of_lt_of_le h1 hij) h2
  · exact zero_le _
  · exact le_refl _

noncomputable def invCdf {m : ℕ} [NeZero m] (p : PMF (Fin m)) (x : ℝ≥0∞) : Fin m :=
  (Finset.univ.filter (fun (i : Fin m) => cdf p i ≤ x)).max' (by
    unfold Finset.Nonempty
    refine ⟨(⟨0, Nat.pos_of_neZero m⟩ : Fin m), ?_⟩
    simp
  )

theorem invCdf_eq_iff {m : ℕ} [NeZero m] (p : PMF (Fin m)) (x : ℝ≥0∞) (hx : x < 1) (i : Fin m) :
    invCdf p x = i ↔ cdf p i ≤ x ∧ x < cdf p (i + 1) := by
  constructor
  · intro h
    unfold invCdf at h
    rw [Finset.max'_eq_iff] at h
    constructor
    · have h := h.1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    · have h := h.2
      by_cases hi : i + 1 < m
      · specialize h ⟨i + 1, hi⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
        by_contra hcontra
        rw [not_lt] at hcontra
        specialize h hcontra
        rw [← Fin.val_fin_le] at h
        simp at h
      · have hi : i + 1 = m := by omega
        rw [hi, cdf_one]
        trivial
  · rintro ⟨hlo, hhi⟩
    unfold invCdf
    rw [Finset.max'_eq_iff]
    constructor
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlo
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hlt := lt_of_le_of_lt hb hhi
      have hmono := Monotone.reflect_lt (cdf_mono p) hlt
      omega

noncomputable def uniformApprox {m : ℕ} [NeZero m]
    (p : PMF (Fin m)) (n : ℕ) [NeZero n] :
    Fin n → Fin m :=
  fun i => invCdf p ((i : ℝ≥0∞) / n)

/-- The number of naturals in [a, b) is at most ⌊b⌋ - ⌈a⌉ + 1 ≤ b - a + 1. -/
private lemma card_nat_in_Ico (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    ((Finset.univ.filter (fun j : Fin n =>
      a ≤ (j : ℝ) ∧ (j : ℝ) < b)).card : ℝ) ≤ b - a + 1 := by
  by_cases hS : (Finset.univ.filter (fun j : Fin n =>
      a ≤ (j : ℝ) ∧ (j : ℝ) < b)).card = 0
  · simp [hS]; linarith
  set S := Finset.univ.filter (fun j : Fin n => a ≤ (j : ℝ) ∧ (j : ℝ) < b)
  have hne : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hS)
  set jlo := (S.min' hne : ℕ)
  set jhi := (S.max' hne : ℕ)
  have hlo_mem := Finset.min'_mem S hne
  have hhi_mem := Finset.max'_mem S hne
  have hlo_ge : a ≤ jlo := ((Finset.mem_filter.mp hlo_mem).2).1
  have hhi_lt : (jhi : ℝ) < b := ((Finset.mem_filter.mp hhi_mem).2).2
  have hle : jlo ≤ jhi := (Finset.min'_le S _ hhi_mem)
  -- S maps injectively (via Fin.val) into Finset.Icc jlo jhi in ℕ
  have hcard_le : S.card ≤ jhi - jlo + 1 := by
    calc S.card
        = (Finset.image Fin.val S).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (Finset.Icc jlo jhi).card := by
          apply Finset.card_le_card
          intro k hk
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
          exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hj, Finset.le_max' _ _ hj⟩
      _ = jhi - jlo + 1 := by simp; omega
  calc (S.card : ℝ) ≤ (jhi - jlo + 1 : ℕ) := by exact_mod_cast hcard_le
    _ = (jhi : ℝ) - (jlo : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hle]; simp
    _ ≤ b - a + 1 := by linarith

theorem uniformApprox_approx {m : ℕ} [NeZero m] (p : PMF (Fin m)) (n : ℕ) [NeZero n] (i : Fin m) :
    ((Finset.univ.filter (fun j : Fin n => uniformApprox p n j = i)).card : ℝ) / n
      ≤ (p i).toReal + 1 / n := by
  -- Characterize the preimage: invCdf p (j/n) = i iff cdf p i ≤ j/n < cdf p (i+1)
  -- Convert ENNReal div conditions to ℝ mul conditions: cdf.toReal*n ≤ j < cdf(i+1).toReal*n
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hcdf_le : cdf p i ≤ cdf p (i + 1) := cdf_mono p (Nat.le_succ _)
  have hcdf_le1 : cdf p (i + 1) ≤ 1 := by
    calc cdf p (i + 1) ≤ cdf p m := cdf_mono p (by omega)
      _ = 1 := cdf_one p
  have hcdf_fin : cdf p i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hcdf_le.trans hcdf_le1)
  have hcdf1_fin : cdf p (i + 1) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hcdf_le1
  have hset : Finset.univ.filter (fun j : Fin n => uniformApprox p n j = i) ⊆
      Finset.univ.filter (fun j : Fin n =>
        (cdf p i).toReal * n ≤ (j : ℝ) ∧ (j : ℝ) < (cdf p (i + 1)).toReal * n) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, uniformApprox] at hj ⊢
    have hlt : (j : ℝ≥0∞) / n < 1 := by
      rw [ENNReal.div_lt_iff (by simp [NeZero.ne n]) (by simp)]
      simp [show (j : ℕ) < n from j.isLt]
    obtain ⟨hlo, hhi⟩ := (invCdf_eq_iff p _ hlt i).mp hj
    have hjn_toReal : ((j : ℝ≥0∞) / n).toReal = (j : ℝ) / n := by
      rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    constructor
    · -- cdf p i ≤ j/n (ENNReal) → cdf.toReal * n ≤ j (ℝ)
      rw [← le_div_iff₀ hn_pos]
      rw [← hjn_toReal]
      exact ENNReal.toReal_mono (ne_top_of_lt hlt) hlo
    · -- j/n < cdf p (i+1) (ENNReal) → j < cdf(i+1).toReal * n (ℝ)
      rw [← div_lt_iff₀ hn_pos, ← hjn_toReal]
      exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hlt) hcdf1_fin).mpr hhi
  have hcard := Finset.card_le_card hset
  -- Apply the ℝ counting lemma
  have hab_real : (cdf p i).toReal ≤ (cdf p (i + 1)).toReal :=
    (ENNReal.toReal_le_toReal hcdf_fin hcdf1_fin).mpr hcdf_le
  have hint := card_nat_in_Ico n ((cdf p i).toReal * n) ((cdf p (i + 1)).toReal * n)
    (mul_le_mul_of_nonneg_right hab_real (Nat.cast_nonneg _))
  -- cdf p (i+1).toReal - cdf p i.toReal = (p i).toReal
  have hdiff : (cdf p (↑i + 1)).toReal - (cdf p i).toReal = (p i).toReal := by
    rw [cdf_succ, ENNReal.toReal_add hcdf_fin (PMF.apply_lt_top p _).ne, add_sub_cancel_left]
  calc ((Finset.univ.filter _).card : ℝ) / n
      ≤ ((Finset.univ.filter _).card : ℝ) / n :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard) hn_pos.le
    _ ≤ ((cdf p (i + 1)).toReal * n - (cdf p i).toReal * n + 1) / n :=
        div_le_div_of_nonneg_right hint hn_pos.le
    _ = (p i).toReal + 1 / n := by rw [← hdiff]; field_simp


/-- For any finite type `Ω` with a probability measure and any `δ > 0`,
there exist `n` and `φ : CoinTape n → Ω` such that for any set `S`,
the pushforward measure exceeds the true measure by at most `δ`. -/
theorem single_coin_approx
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (φ : CoinTape n → Ω),
      ∀ (S : Set Ω),
        volume.real (φ ⁻¹' S : Set (CoinTape n)) ≤
        volume.real S + δ := by
  classical
  set k := Fintype.card Ω with hk_def
  have hk_pos : 0 < k := Fintype.card_pos
  haveI : NeZero k := ⟨by omega⟩
  -- Choose n with k / 2^n ≤ δ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (k : ℝ) / 2 ^ n ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (div_pos hδ (Nat.cast_pos.mpr hk_pos)) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, le_of_lt ?_⟩
    have : (1 / 2 : ℝ) ^ n * k < δ := by rwa [lt_div_iff₀ (by positivity)] at hn
    linarith [show (k : ℝ) / 2 ^ n = (1 / 2) ^ n * k from by
      rw [one_div, inv_pow, inv_mul_eq_div]]
  use n
  set N := Fintype.card (CoinTape n)
  have hN_pos : 0 < N := Fintype.card_pos
  haveI : NeZero N := ⟨by omega⟩
  have hN_eq : N = 2 ^ n := by simp [N, Fintype.card_fin]
  -- PMF on Fin k from the measure on Ω
  set e := Fintype.equivFin Ω
  have hpmf : HasSum (fun i : Fin k => volume ({e.symm i} : Set Ω)) 1 :=
    FiniteProbabilitySpace.hasSum_measure_singletons e
  set q : PMF (Fin k) := ⟨fun i => volume ({e.symm i} : Set Ω), hpmf⟩
  -- φ: CoinTape n ≃ Fin N → uniformApprox → Fin k → e.symm → Ω
  set eC : CoinTape n ≃ Fin N := Fintype.equivFin _
  refine ⟨fun c => e.symm (uniformApprox q N (eC c)), fun S => ?_⟩
  set φ := fun c => e.symm (uniformApprox q N (eC c))
  set g := fun c : CoinTape n => uniformApprox q N (eC c)
  set S_idx := Finset.univ.filter (fun i : Fin k => e.symm i ∈ S)
  -- Per-element bound (bijected via eC)
  have helem : ∀ i : Fin k,
      ((Finset.univ.filter (fun c : CoinTape n => g c = i)).card : ℝ) / N ≤
      (q i).toReal + 1 / N := by
    intro i
    rw [show (Finset.univ.filter (fun c : CoinTape n => g c = i)).card =
      (Finset.univ.filter (fun j : Fin N => uniformApprox q N j = i)).card from
      Finset.card_equiv eC (fun c => by simp [g])]
    exact uniformApprox_approx q N i
  -- Fiber decomposition: {c | φ c ∈ S} partitions by g(c) value
  have hfiber : (Finset.univ.filter (fun c : CoinTape n => φ c ∈ S)).card =
      ∑ i ∈ S_idx, (Finset.univ.filter (fun c : CoinTape n => g c = i)).card := by
    have : ∀ c : CoinTape n, φ c ∈ S ↔ g c ∈ S_idx := by
      intro c; simp [φ, g, S_idx]
    rw [show Finset.univ.filter (fun c => φ c ∈ S) =
      Finset.univ.filter (fun c => g c ∈ S_idx) from Finset.filter_congr (fun c _ => this c)]
    exact (Finset.sum_card_fiberwise_eq_card_filter _ _ _).symm
  -- CoinTape volume = counting / N
  have hvol_pre : volume.real (φ ⁻¹' S : Set (CoinTape n)) =
      ((Finset.univ.filter (fun c : CoinTape n => φ c ∈ S)).card : ℝ) / N := by
    simpa [N, Set.mem_preimage] using
      uniformOn_univ_measureReal_eq_card_filter
        (Ω := CoinTape n) (φ ⁻¹' S : Set (CoinTape n))
  -- Volume of S as sum of q
  have hvol_S : volume.real S = ∑ i ∈ S_idx, (q i).toReal := by
    have hpre : e ⁻¹' (↑S_idx : Set (Fin k)) = S := by
      ext x
      change (e x ∈ S_idx) ↔ x ∈ S
      simp [S_idx]
    rw [← hpre]
    rw [FiniteProbabilitySpace.measureReal_preimage_finset
      (Ξ := Ω) (Ω := Fin k) e S_idx]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hs : e ⁻¹' ({i} : Set (Fin k)) = ({e.symm i} : Set Ω) := by
      ext x
      constructor
      · intro hx
        simpa using congrArg e.symm hx
      · intro hx
        subst x
        exact e.apply_symm_apply i
    rw [hs]
    rfl
  -- Combine
  rw [hvol_pre, hfiber]; push_cast
  have hN_pos_real : (0 : ℝ) < N := by positivity
  -- (∑ f_i) / N ≤ vol(S) + δ, using per-element bound
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos_real
  calc (∑ x ∈ S_idx, ((Finset.univ.filter (fun c => g c = x)).card : ℝ)) / N
      = ∑ x ∈ S_idx, ((Finset.univ.filter (fun c => g c = x)).card : ℝ) / N := by
        simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
    _ ≤ ∑ i ∈ S_idx, ((q i).toReal + 1 / N) :=
        Finset.sum_le_sum (fun i _ => helem i)
    _ = (∑ i ∈ S_idx, (q i).toReal) + S_idx.card / N := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ volume.real S + k / N := by
        rw [hvol_S]
        have hcard : (S_idx.card : ℝ) ≤ k := by
          have h := S_idx.card_le_univ; simp only [Fintype.card_fin] at h; exact_mod_cast h
        linarith [div_le_div_of_nonneg_right hcard hN_pos_real.le]
    _ ≤ volume.real S + δ := by
        have : (k : ℝ) / N ≤ δ := by rw [hN_eq]; push_cast; exact hn
        linarith

/-- If p approximates q (∑_{a∈T} p(a) ≤ ∑_{a∈T} q(a) + δ for all T)
and g : α → ℝ with 0 ≤ g ≤ 1, then ∑ p(a)*g(a) ≤ ∑ q(a)*g(a) + δ.
Used in the product coin approximation. -/
private lemma weighted_sum_approx {α : Type*} [Fintype α]
    (p q : α → ℝ) (g : α → ℝ)
    (hg_nn : ∀ a, 0 ≤ g a) (hg_le1 : ∀ a, g a ≤ 1)
    (hδ : ℝ)
    (happrox : ∀ T : Finset α, ∑ a ∈ T, p a ≤ ∑ a ∈ T, q a + hδ) :
    ∑ a, p a * g a ≤ ∑ a, q a * g a + hδ := by
  -- Split into A⁺ = {a | q a < p a} and complement
  set Apos := Finset.univ.filter (fun a => q a < p a)
  suffices h : ∑ a, (p a - q a) * g a ≤ hδ by
    have : ∑ a, p a * g a - ∑ a, q a * g a = ∑ a, (p a - q a) * g a := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext a; ring
    linarith
  rw [(Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => q a < p a) _).symm]
  -- Complement: (p-q)*g ≤ 0
  have h_neg : ∑ a ∈ Finset.univ.filter (fun a => ¬(q a < p a)),
      (p a - q a) * g a ≤ 0 := Finset.sum_nonpos (fun a ha =>
    mul_nonpos_of_nonpos_of_nonneg (by linarith [(Finset.mem_filter.mp ha).2]) (hg_nn a))
  -- A⁺: (p-q)*g ≤ (p-q) since g ≤ 1
  have h_pos : ∑ a ∈ Apos, (p a - q a) * g a ≤ ∑ a ∈ Apos, (p a - q a) :=
    Finset.sum_le_sum (fun a ha =>
      mul_le_of_le_one_right (by linarith [(Finset.mem_filter.mp ha).2]) (hg_le1 a))
  -- ∑_{A⁺} (p-q) ≤ δ (from happrox applied to A⁺)
  have h_approx : ∑ a ∈ Apos, (p a - q a) ≤ hδ := by
    have := happrox Apos
    have hsub : ∑ a ∈ Apos, (p a - q a) = ∑ a ∈ Apos, p a - ∑ a ∈ Apos, q a := by
      rw [← Finset.sum_sub_distrib]
    linarith [hsub]
  linarith

private theorem product_coin_approx
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (nX nY : ℕ) (φ_X : CoinTape nX → Ω_X)
      (φ_Y : CoinTape nY → Ω_Y),
      ∀ (S : Set (Ω_X × Ω_Y)),
        volume.real (Prod.map φ_X φ_Y ⁻¹' S :
          Set (CoinTape nX × CoinTape nY)) ≤
        volume.real S + δ := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  obtain ⟨nX, φ_X, hX⟩ := single_coin_approx (Ω := Ω_X) (δ / 2) hδ2
  obtain ⟨nY, φ_Y, hY⟩ := single_coin_approx (Ω := Ω_Y) (δ / 2) hδ2
  refine ⟨nX, nY, φ_X, φ_Y, fun S => ?_⟩
  -- Slice: S_a = {b | (a,b) ∈ S}
  set S_a : Ω_X → Set Ω_Y := fun a => Prod.mk a ⁻¹' S
  -- Decompose preimage as union of rectangles
  have hunion : (Prod.map φ_X φ_Y ⁻¹' S : Set (CoinTape nX × CoinTape nY)) =
      ⋃ a : Ω_X, (φ_X ⁻¹' {a}) ×ˢ (φ_Y ⁻¹' S_a a) := by
    ext ⟨cx, cy⟩; simp [S_a, Set.mem_preimage, Set.mem_iUnion]
  have hdisj : Pairwise (fun a b : Ω_X => Disjoint
      ((φ_X ⁻¹' {a}) ×ˢ (φ_Y ⁻¹' S_a a)) ((φ_X ⁻¹' {b}) ×ˢ (φ_Y ⁻¹' S_a b))) := by
    intro a b hab; rw [Set.disjoint_left]
    rintro ⟨cx, cy⟩ h1 h2
    have hcx : φ_X cx = a := by
      simpa only [Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff] using h1.1
    have hcx' : φ_X cx = b := by
      simpa only [Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff] using h2.1
    exact hab (hcx.symm.trans hcx')
  -- LHS = ∑_a vol(φ_X⁻¹({a})) * vol(φ_Y⁻¹(S_a))
  have hLHS : volume.real (Prod.map φ_X φ_Y ⁻¹' S :
      Set (CoinTape nX × CoinTape nY)) =
      ∑ a : Ω_X, volume.real (φ_X ⁻¹' {a} : Set (CoinTape nX)) *
        volume.real (φ_Y ⁻¹' S_a a : Set (CoinTape nY)) := by
    rw [hunion, FiniteProbabilitySpace.measureReal_iUnion_fintype _ hdisj]
    refine Finset.sum_congr rfl ?_
    intro a ha
    simpa using FiniteProbabilitySpace.measureReal_prod
      (φ_X ⁻¹' ({a} : Set Ω_X)) (φ_Y ⁻¹' S_a a)
  -- RHS = ∑_a vol({a}) * vol(S_a)
  have hRHS : volume.real S = ∑ a : Ω_X, volume.real ({a} : Set Ω_X) *
      volume.real (S_a a) := by
    have hS : S = ⋃ a : Ω_X, ({a} : Set Ω_X) ×ˢ S_a a := by
      ext ⟨x, y⟩; simp [S_a]
    have hdisj' : Pairwise (fun a b : Ω_X => Disjoint
        (({a} : Set Ω_X) ×ˢ S_a a) (({b} : Set Ω_X) ×ˢ S_a b)) := by
      intro a b hab; rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      have hx : x = a := by
        simpa only [Set.mem_prod, Set.mem_singleton_iff] using h1.1
      have hx' : x = b := by
        simpa only [Set.mem_prod, Set.mem_singleton_iff] using h2.1
      exact hab (hx.symm.trans hx')
    rw [hS, FiniteProbabilitySpace.measureReal_iUnion_fintype _ hdisj']
    refine Finset.sum_congr rfl ?_
    intro a ha
    simpa using FiniteProbabilitySpace.measureReal_prod ({a} : Set Ω_X) (S_a a)
  -- Step 1: bound using hY on each slice
  set pX := fun a => volume.real (φ_X ⁻¹' {a} : Set (CoinTape nX))
  set qX := fun a => volume.real ({a} : Set Ω_X)
  rw [hLHS]
  have hstep1 : ∑ a : Ω_X, pX a * volume.real (φ_Y ⁻¹' S_a a : Set (CoinTape nY)) ≤
      ∑ a : Ω_X, pX a * (volume.real (S_a a) + δ / 2) :=
    Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hY _)
      (by simp [pX, Measure.real]))
  -- ∑ pX * (g + δ/2) = ∑ pX * g + δ/2 (since ∑ pX = 1)
  have hpX_sum : ∑ a : Ω_X, pX a = 1 := by
    calc ∑ a : Ω_X, pX a
        = volume.real (φ_X ⁻¹' (Set.univ : Set Ω_X) : Set (CoinTape nX)) := by
            symm
            simpa [pX] using
              (FiniteProbabilitySpace.measureReal_preimage_finset
                (Ξ := CoinTape nX) (Ω := Ω_X) φ_X Finset.univ)
      _ = 1 := by simp
  have hexpand : ∑ a, pX a * (volume.real (S_a a) + δ / 2) =
      (∑ a, pX a * volume.real (S_a a)) + δ / 2 := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hpX_sum, one_mul]
  -- Step 2: bound ∑ pX * g ≤ ∑ qX * g + δ/2 using weighted_sum_approx
  set gval := fun a : Ω_X => volume.real (S_a a)
  have hstep2 : ∑ a, pX a * gval a ≤ ∑ a, qX a * gval a + δ / 2 := by
    apply weighted_sum_approx pX qX gval
      (fun _ => MeasureTheory.measureReal_nonneg)
      (fun a => by
        calc gval a = volume.real (S_a a) := rfl
          _ ≤ volume.real (Set.univ : Set Ω_Y) := by
              rw [Measure.real, Measure.real]
              exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
          _ = 1 := by simp)
      (δ / 2)
      (fun T => by
        have := hX (↑T : Set Ω_X)
        simp only [pX, qX]
        -- Convert both finite-set measures into sums over singleton fibers.
        rw [FiniteProbabilitySpace.measureReal_preimage_finset
          (Ξ := CoinTape nX) (Ω := Ω_X) φ_X T] at this
        rw [FiniteProbabilitySpace.measureReal_finset (Ω := Ω_X) T] at this
        linarith)
  calc ∑ a, pX a * volume.real (φ_Y ⁻¹' S_a a : Set (CoinTape nY))
      ≤ (∑ a, pX a * gval a) + δ / 2 := by linarith [hstep1, hexpand]
    _ ≤ (∑ a, qX a * gval a) + δ / 2 + δ / 2 := by linarith [hstep2]
    _ = (∑ a, qX a * gval a) + δ := by ring
    _ = volume.real S + δ := by rw [hRHS]

end Internal

namespace PrivateCoin

/-- Approximate a finite-message protocol over arbitrary finite
probability spaces by one over CoinTape. Given `δ > 0`, produces
`nX`, `nY`, and a CoinTape-based protocol with the same complexity
whose run approximates the original (via inverse CDF construction).
This does not depend on any predicate Q. -/
noncomputable def FiniteMessage.Protocol.toCoinTape
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    Σ (nX : ℕ) (nY : ℕ),
      FiniteMessage.Protocol (CoinTape nX) (CoinTape nY) X Y α :=
  let data := Internal.product_coin_approx (Ω_X := Ω_X) (Ω_Y := Ω_Y) δ hδ
  let nX := data.choose
  let nY := data.choose_spec.choose
  let φ_X := data.choose_spec.choose_spec.choose
  let φ_Y := data.choose_spec.choose_spec.choose_spec.choose
  ⟨nX, nY, p.comap (Prod.map φ_X id) (Prod.map φ_Y id)⟩

@[simp]
theorem FiniteMessage.Protocol.toCoinTape_complexity
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    (p.toCoinTape δ hδ).2.2.complexity = p.complexity := by
  simp [FiniteMessage.Protocol.toCoinTape]

/-- The CoinTape approximation of a protocol preserves ApproxSatisfies
up to the given slack δ. -/
theorem FiniteMessage.Protocol.toCoinTape_approxSatisfies
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (Q : X → Y → α → Prop)
    (ε δ : ℝ) (hδ : 0 < δ)
    (hp : p.ApproxSatisfies Q ε) :
    (p.toCoinTape δ hδ).2.2.ApproxSatisfies Q (ε + δ) := by
  intro x y
  simp only [FiniteMessage.Protocol.toCoinTape]
  -- Extract the approximation data
  set data := Internal.product_coin_approx (Ω_X := Ω_X) (Ω_Y := Ω_Y) δ hδ
  set φ_X := data.choose_spec.choose_spec.choose
  set φ_Y := data.choose_spec.choose_spec.choose_spec.choose
  have happrox := data.choose_spec.choose_spec.choose_spec.choose_spec
  -- The error set under the new protocol is the preimage under (φ_X, φ_Y)
  let S := {ω : Ω_X × Ω_Y | ¬Q x y (p.rrun x y ω.1 ω.2)}
  have hset : {ω : CoinTape data.choose × CoinTape data.choose_spec.choose |
      ¬Q x y (FiniteMessage.Protocol.rrun
        (p.comap (Prod.map φ_X id) (Prod.map φ_Y id)) x y ω.1 ω.2)} =
      Prod.map φ_X φ_Y ⁻¹' S := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Prod.map, S,
      FiniteMessage.Protocol.rrun,
      Deterministic.FiniteMessage.Protocol.comap_run, Function.id_def]
  rw [hset]
  calc volume.real (Prod.map φ_X φ_Y ⁻¹' S :
          Set (CoinTape data.choose × CoinTape data.choose_spec.choose))
      ≤ volume.real S + δ := happrox S
    _ ≤ ε + δ := by
        have hpS : volume.real S ≤ ε := by simpa [S] using hp x y
        linarith

end PrivateCoin

end CommunicationComplexity
