/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty, Mina Sha
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Junta
import TCSlib.BooleanAnalysis.LMN.FourierConcentration
import TCSlib.BooleanAnalysis.LMN.CircuitHelpers
import TCSlib.BooleanAnalysis.LMN.SwitchingBernoulli
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourier concentration and junta approximation for DNFs

## Main definitions

No new definitions.

## Main results

* `dnf_fourierWeightAbove_le`: a regular width-`w` DNF has squared Fourier
  weight at most `8 * (1 / 2) ^ t` above degree `120 * w * (t + 1)`.
* `dnf_fourierWeightAbove_le_of_width`: the same bound for arbitrary bounded-width DNFs.
* `dnf_sensitivity_true_le_width`: a satisfying input has sensitivity at most the DNF width.
* `dnf_totalInfluence_le_two_mul_width`: total influence is at most twice the width.
* `dnf_junta_parameters`: dyadic cutoffs give uniform polynomial size bounds.
* `dnf_junta`: bounded-width DNFs admit polynomial-size junta approximation.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §4.2, Lemma 4.21 and Corollary 9.30.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

/-- A width-`w` DNF with consistent, duplicate-free terms has squared Fourier weight
at most `8 * (1 / 2) ^ t` above degree `120 * w * (t + 1)`, for every positive `w`
and natural `t`. [OD14, Lemma 4.21; Cor. 9.30]
The constants `120` and `8` are convenient explicit enlargements of the source bound.
The statement retains the regularity hypotheses of the switching estimate and
includes the zero-dimensional cube and `t = 0`.

**Proof sketch.** Write `K = 120w(t + 1)`. If the dimension is at most `K`, the
Fourier tail is empty. Otherwise take restriction parameter `p = 1/(40w)` and
apply the restriction-to-Fourier estimate at depth `t + 1`. The desired tail lies
inside its spectral tail, while the corresponding depth event is depth greater
than `t`. The Bernoulli switching estimate bounds its probability by
`2⁻ᵗ + exp(-np/3)`. Since the dimension exceeds `K`, we have `np/3 > t + 1`,
so the exponential term is at most `2⁻ᵗ`. Multiplication by the
restriction-to-Fourier factor four gives the claimed bound. -/
theorem dnf_fourierWeightAbove_le {n : ℕ} (d : DNF n) (w : ℕ)
    (hw : d.width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ u ∈ d.terms, ∀ l₁ ∈ u, ∀ l₂ ∈ u, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ u ∈ d.terms, u.Nodup) (t : ℕ) :
    ThresholdFunctions.fourierWeightAbove (120 * w * (t + 1))
      (fun x => boolToSign (d.eval x)) ≤ 8 * (1 / 2 : ℝ) ^ t :=
  (by
  classical
  let K : ℕ := 120 * w * (t + 1)
  change ThresholdFunctions.fourierWeightAbove K
    (fun x => boolToSign (d.eval x)) ≤ 8 * (1 / 2 : ℝ) ^ t
  by_cases hn : n ≤ K
  · have hzero : ThresholdFunctions.fourierWeightAbove K
        (fun x => boolToSign (d.eval x)) = 0 := by
      unfold ThresholdFunctions.fourierWeightAbove
      apply Finset.sum_eq_zero
      intro S _
      have hcard : S.card ≤ n := by
        simpa using Finset.card_le_univ S
      have hnot : ¬ K < S.card := by omega
      simp [hnot]
    rw [hzero]
    positivity
  · have hnpos : 0 < n := by omega
    have hwR : 0 < (w : ℝ) := by exact_mod_cast hw_pos
    let p : ℝ := 1 / (40 * (w : ℝ))
    have hp : 0 < p := by
      dsimp [p]
      positivity
    have hp_one : p ≤ 1 := by
      have hwone : (1 : ℝ) ≤ (w : ℝ) := by
        exact_mod_cast (show 1 ≤ w by omega)
      dsimp [p]
      apply (div_le_iff₀ (by positivity)).mpr
      linarith only [hwone]
    have hcutoff (m : ℕ) (hm : K < m) :
        3 * ((t : ℝ) + 1) ≤ p * (m : ℝ) := by
      have hmR : 120 * (w : ℝ) * ((t : ℝ) + 1) < (m : ℝ) := by
        exact_mod_cast (show 120 * w * (t + 1) < m from hm)
      have hdiv : 3 * ((t : ℝ) + 1) ≤ (m : ℝ) / (40 * (w : ℝ)) := by
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith only [hmR]
      simpa [p, div_eq_mul_inv, mul_comm] using hdiv
    have htransfer := RestrictionFourier.odonnell_lemma_4_21
      d.eval p hp.le hp_one (t + 1) (by omega)
    simp only [Nat.succ_le_iff] at htransfer
    have hswitch := SwitchingBernoulli.switching_bernoulli_dtDepth_dnf
      d w hw hw_pos hnd hnodup hnpos p hp le_rfl hp_one t
    have htail :
        ThresholdFunctions.fourierWeightAbove K (fun x => boolToSign (d.eval x)) ≤
          ∑ S : Finset (Fin n),
            if 3 * ((t + 1 : ℕ) : ℝ) ≤ p * (S.card : ℝ)
            then fourierCoeff (fun x => boolToSign (d.eval x)) S ^ 2 else 0 := by
      unfold ThresholdFunctions.fourierWeightAbove
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : K < S.card
      · have hcondition : 3 * ((t + 1 : ℕ) : ℝ) ≤ p * (S.card : ℝ) := by
          simpa using hcutoff S.card hS
        rw [if_pos hS, if_pos hcondition]
      · rw [if_neg hS]
        split_ifs <;> positivity
    have hhalf : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
      have htwo : 2 ≤ Real.exp 1 := by
        linarith only [Real.add_one_le_exp 1]
      rw [Real.exp_neg]
      simpa only [one_div] using
        one_div_le_one_div_of_le (show 0 < (2 : ℝ) by norm_num) htwo
    have hexp : Real.exp (-((n : ℝ) * p / 3)) ≤ (1 / 2 : ℝ) ^ t := by
      calc
        Real.exp (-((n : ℝ) * p / 3)) ≤ Real.exp (-(t : ℝ)) := by
          apply Real.exp_le_exp.mpr
          linarith only [hcutoff n (by omega)]
        _ = Real.exp (-1) ^ t := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        _ ≤ (1 / 2 : ℝ) ^ t :=
          pow_le_pow_left₀ (Real.exp_nonneg _) hhalf t
    linarith only [htail, htransfer, hswitch, hexp]
)

/-- For every width-`w` DNF with positive `w`, the squared Fourier weight above
degree `120 * w * (t + 1)` is at most `8 * (1 / 2) ^ t`. [OD14, Cor. 9.30]
The sign encoding sends true to `-1`. The constants are explicit convenient
enlargements of the source bound, and the statement includes `n = 0` and `t = 0`.

**Proof sketch.** Replace the DNF by its cleaned form, which has the same evaluation,
no greater width, and consistent, duplicate-free terms. Apply the regular-DNF
Fourier-tail bound to that formula and transfer the conclusion through equality
of the represented functions. -/
lemma dnf_fourierWeightAbove_le_of_width {n : ℕ} (d : DNF n) (w : ℕ)
    (hw : d.width ≤ w) (hw_pos : 0 < w) (t : ℕ) :
    ThresholdFunctions.fourierWeightAbove (120 * w * (t + 1))
      (fun x => boolToSign (d.eval x)) ≤ 8 * (1 / 2 : ℝ) ^ t :=
  (by
  simpa only [LMN.cleanDNF_eval] using
    dnf_fourierWeightAbove_le (LMN.cleanDNF d) w
      ((LMN.cleanDNF_width_le d).trans hw) hw_pos
      (LMN.cleanDNF_var_inj d) (LMN.cleanDNF_nodup d) t
)

/-- At every satisfying input of a DNF, the sensitivity of its sign encoding is
at most the formula's width. [OD14, Def. 4.1; Cor. 9.30, proof]
This certificate estimate requires no term-regularity or positive-width assumption
and includes the zero-dimensional cube.

**Proof sketch.** Choose a term satisfied by the input. Flipping a coordinate absent
from that term preserves every literal in the term, so the term remains satisfied
and the DNF value stays true. Thus every sensitive coordinate occurs in the chosen
term. The number of distinct variables in that term is at most its length, which
is at most the DNF's width. -/
lemma dnf_sensitivity_true_le_width {n : ℕ} (d : DNF n) (x : BoolCube n)
    (hx : d.eval x = true) :
    sensitivity (fun y => boolToSign (d.eval y)) x ≤ d.width :=
  (by
  classical
  obtain ⟨u, hu, hux⟩ :
      ∃ u ∈ d.terms, Term.eval u x = true :=
    List.any_eq_true.mp hx
  have hsupport :
      (Finset.univ.filter (fun i =>
        boolToSign (d.eval x) ≠ boolToSign (d.eval (flipBit x i)))) ⊆
        (u.map Literal.var).toFinset := by
    intro i hi
    by_contra hn
    have hvar (l : Literal n) (hl : l ∈ u) : i ≠ l.var := by
      intro heq
      apply hn
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr ⟨l, hl, heq.symm⟩
    have hterm : Term.eval u (flipBit x i) = true := by
      apply List.all_eq_true.mpr
      intro l hl
      have heval : l.eval (flipBit x i) = l.eval x := by
        simp only [Literal.eval, flipBit_ne x i l.var (hvar l hl)]
      rw [heval]
      exact (List.all_eq_true.mp hux) l hl
    have hdtrue : d.eval (flipBit x i) = true :=
      List.any_eq_true.mpr ⟨u, hu, hterm⟩
    exact (Finset.mem_filter.mp hi).2 (by rw [hx, hdtrue])
  calc
    sensitivity (fun y => boolToSign (d.eval y)) x ≤
        (u.map Literal.var).toFinset.card :=
      Finset.card_le_card hsupport
    _ ≤ u.length := by
      simpa using List.toFinset_card_le (u.map Literal.var)
    _ ≤ d.width := SwitchingLemma.term_length_le_width d u hu
)

/-- The total influence of the sign encoding of any DNF is at most twice its width.
[OD14, Cor. 9.30, proof]
This explicit certificate bound includes width zero and the zero-dimensional cube.

**Proof sketch.** Flipping a coordinate pairs the two endpoints of every boundary
edge, so its satisfying and falsifying endpoints contribute equally under the
uniform measure. Total influence is therefore twice the expected number of
sensitive coordinates at satisfying inputs, with zero contribution at other
inputs. At each satisfying input that number is at most the DNF's width.
Taking expectations gives the bound. -/
lemma dnf_totalInfluence_le_two_mul_width {n : ℕ} (d : DNF n) :
    totalInfluence (fun x => boolToSign (d.eval x)) ≤ 2 * (d.width : ℝ) :=
  (by
  classical
  let A : Fin n → BoolCube n → ℕ := fun i x =>
    if d.eval x = true ∧ d.eval (flipBit x i) = false then 1 else 0
  -- Pair the two endpoints of each edge.
  have hedge (i : Fin n) :
      influence i (fun x => boolToSign (d.eval x)) =
        2 * expect (fun x => (A i x : ℝ)) := by
    have hflip :
        expect (fun x => (A i (flipBit x i) : ℝ)) =
          expect (fun x => (A i x : ℝ)) := by
      simp_rw [expect_eq_fintypeExpect]
      exact Fintype.expect_bijective
        (fun x : BoolCube n => flipBit x i)
        (show Function.Involutive (fun x : BoolCube n => flipBit x i) from
          fun x => flipBit_flipBit x i).bijective
        (fun x => (A i (flipBit x i) : ℝ))
        (fun x => (A i x : ℝ)) (fun _ => rfl)
    have hpoint (x : BoolCube n) :
        (boolToSign (d.eval x) - boolToSign (d.eval (flipBit x i))) ^ 2 / 4 =
          (A i x : ℝ) + (A i (flipBit x i) : ℝ) := by
      dsimp [A]
      rw [flipBit_flipBit]
      cases hx : d.eval x <;> cases hy : d.eval (flipBit x i) <;>
        norm_num [boolToSign, hx, hy]
    rw [influence]
    simp_rw [hpoint]
    rw [ThresholdFunctions.expect_add, hflip]
    ring
  -- At a satisfying input, the one-sided count is its sensitivity.
  have hmean :
      expect (fun x => ∑ i : Fin n, (A i x : ℝ)) ≤ (d.width : ℝ) := by
    calc
      expect (fun x => ∑ i : Fin n, (A i x : ℝ)) ≤
          expect (fun _ : BoolCube n => (d.width : ℝ)) := by
        apply ThresholdFunctions.expect_mono
        intro x
        have hnat : (∑ i : Fin n, A i x) ≤ d.width := by
          by_cases hx : d.eval x = true
          · calc
              (∑ i : Fin n, A i x) =
                  sensitivity (fun y => boolToSign (d.eval y)) x := by
                rw [sensitivity, Finset.card_filter]
                apply Finset.sum_congr rfl
                intro i _
                cases hy : d.eval (flipBit x i) <;>
                  norm_num [A, hx, hy, boolToSign]
              _ ≤ d.width := dnf_sensitivity_true_le_width d x hx
          · simp [A, hx]
        exact_mod_cast hnat
      _ = (d.width : ℝ) := ThresholdFunctions.expect_const _
  -- Sum the edge identities and exchange the finite sum with expectation.
  calc
    totalInfluence (fun x => boolToSign (d.eval x)) =
        2 * expect (fun x => ∑ i : Fin n, (A i x : ℝ)) := by
      unfold totalInfluence
      simp_rw [hedge]
      rw [← Finset.mul_sum]
      simp_rw [expect_eq_fintypeExpect, Finset.expect_sum_comm]
    _ ≤ 2 * (d.width : ℝ) := by linarith only [hmean]
)

/-- An absolute `C > 0` allows every positive width `w` and error `0 < ε ≤ 1/2`
to admit a natural `t` with `8 · 2⁻ᵗ ≤ ε` and
`(2w)³ ε⁻² 9^(120w(t+1)) ≤ (1/ε)^(Cw)`.
This scalar estimate supplies explicit parameters for [OD14, Cor. 9.30].

**Proof sketch.** Set `ℓ = log(1/ε)` and choose
`t = ⌈ℓ / log 2⌉ + 3`. Then the dyadic tail is at most `ε`, and
`t + 1 ≤ 6ℓ / log 2`. Express the remaining factors as exponentials.
The bounds `w ≥ 1` and `ℓ ≥ log 2` absorb their exponents into one
absolute constant times `wℓ`. -/
lemma dnf_junta_parameters :
    ∃ C : ℝ, 0 < C ∧
      ∀ w : ℕ, 0 < w → ∀ ε : ℝ, ε ∈ Set.Ioc 0 (1 / 2) →
        ∃ t : ℕ, 8 * (1 / 2 : ℝ) ^ t ≤ ε ∧
          (2 * (w : ℝ)) ^ 3 / ε ^ 2 * (9 : ℝ) ^ (120 * w * (t + 1)) ≤
            (1 / ε) ^ (C * (w : ℝ)) :=
  (by
  classical
  let L : ℝ := Real.log 2
  let M : ℝ := Real.log 9
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hM : 0 ≤ M := Real.log_nonneg (by norm_num)
  let C : ℝ := 2 + (6 + 720 * M) / L
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro w hw ε hε
  have hεpos : 0 < ε := hε.1
  have hwone : (1 : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast (show 1 ≤ w by omega)
  let ell : ℝ := Real.log (1 / ε)
  have hreciprocal : (2 : ℝ) ≤ 1 / ε := by
    apply (le_div_iff₀ hεpos).mpr
    linarith only [hε.2]
  have hell : L ≤ ell := Real.log_le_log (by norm_num) hreciprocal
  have hellpos : 0 < ell := by linarith only [hell, hL]
  let q : ℝ := ell / L
  have hq : 1 ≤ q := by
    apply (le_div_iff₀ hL).mpr
    linarith only [hell]
  let m : ℕ := ⌈q⌉₊
  let t : ℕ := m + 3
  have hm_lower : q ≤ (m : ℝ) := Nat.le_ceil q
  have hm_upper : (m : ℝ) ≤ q + 1 := by
    have hceil : (m : ℝ) ≤ (⌊q⌋₊ : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_le_floor_add_one q
    have hfloor : (⌊q⌋₊ : ℝ) ≤ q :=
      Nat.floor_le (by linarith only [hq])
    linarith only [hceil, hfloor]
  have htcast : (t : ℝ) = (m : ℝ) + 3 := by
    norm_num [t]
  have htq : (t : ℝ) + 1 ≤ 6 * q := by
    linarith only [htcast, hm_upper, hq]
  -- The upward-rounded logarithmic cutoff gives the desired dyadic tail.
  have htail : 8 * (1 / 2 : ℝ) ^ t ≤ ε := by
    have hhalf : Real.exp (-L) = (1 / 2 : ℝ) := by
      dsimp [L]
      rw [Real.exp_neg, Real.exp_log (by norm_num), ← one_div]
    have hpower : (1 / 2 : ℝ) ^ t = Real.exp (-(t : ℝ) * L) := by
      rw [← hhalf, ← Real.exp_nat_mul]
      congr 1
      ring
    have height : Real.exp (3 * L) = 8 := by
      have hthree : Real.exp (3 * L) = Real.exp L ^ 3 := by
        simpa using (Real.exp_nat_mul L 3)
      rw [hthree]
      dsimp [L]
      rw [Real.exp_log (by norm_num)]
      norm_num
    have hqL : q * L = ell := by
      dsimp [q]
      field_simp [hL.ne']
    have hmL := mul_le_mul_of_nonneg_right hm_lower hL.le
    rw [hqL] at hmL
    calc
      8 * (1 / 2 : ℝ) ^ t =
          Real.exp (3 * L) * Real.exp (-(t : ℝ) * L) := by
        rw [height, hpower]
      _ = Real.exp (3 * L - (t : ℝ) * L) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-ell) := by
        apply Real.exp_le_exp.mpr
        rw [htcast]
        linarith only [hmL]
      _ = ε := by
        dsimp [ell]
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        simp
  -- Absorb the cubic width factor into exponential growth.
  have hwidth : (2 * (w : ℝ)) ^ 3 ≤ Real.exp (6 * (w : ℝ)) := by
    calc
      (2 * (w : ℝ)) ^ 3 ≤ Real.exp (2 * (w : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by positivity)
          (by linarith only [Real.add_one_le_exp (2 * (w : ℝ))]) 3
      _ = Real.exp (6 * (w : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  let K : ℕ := 120 * w * (t + 1)
  have hKcast : (K : ℝ) = 120 * (w : ℝ) * ((t : ℝ) + 1) := by
    norm_num [K]
  have hexponent :
      6 * (w : ℝ) + 2 * ell + (K : ℝ) * M ≤ ell * (C * (w : ℝ)) := by
    have hprefactor := mul_le_mul_of_nonneg_right hq
      (show 0 ≤ 6 * (w : ℝ) by positivity)
    have herror := mul_le_mul_of_nonneg_left hwone
      (show 0 ≤ 2 * ell by positivity)
    have hdegree := mul_le_mul_of_nonneg_left htq
      (show 0 ≤ 120 * (w : ℝ) * M by positivity)
    calc
      6 * (w : ℝ) + 2 * ell + (K : ℝ) * M ≤
          6 * q * (w : ℝ) + 2 * ell * (w : ℝ) +
            720 * (w : ℝ) * q * M := by
        rw [hKcast]
        nlinarith only [hprefactor, herror, hdegree]
      _ = ell * (C * (w : ℝ)) := by
        dsimp [C, q]
        simp only [div_eq_mul_inv]
        ring
  refine ⟨t, htail, ?_⟩
  change (2 * (w : ℝ)) ^ 3 / ε ^ 2 * (9 : ℝ) ^ K ≤
    (1 / ε) ^ (C * (w : ℝ))
  calc
    (2 * (w : ℝ)) ^ 3 / ε ^ 2 * (9 : ℝ) ^ K =
        (2 * (w : ℝ)) ^ 3 * (1 / ε) ^ 2 * (9 : ℝ) ^ K := by
      rw [one_div_pow]
      ring
    _ ≤ Real.exp (6 * (w : ℝ)) * (1 / ε) ^ 2 * (9 : ℝ) ^ K :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hwidth (by positivity)) (by positivity)
    _ = Real.exp (6 * (w : ℝ) + 2 * ell + (K : ℝ) * M) := by
      have htwo : Real.exp (2 * ell) = Real.exp ell ^ 2 := by
        simpa using (Real.exp_nat_mul ell 2)
      rw [Real.exp_add, Real.exp_add, htwo, Real.exp_nat_mul M K]
      dsimp [ell, M]
      rw [Real.exp_log (by positivity), Real.exp_log (by norm_num)]
    _ ≤ Real.exp (ell * (C * (w : ℝ))) :=
      Real.exp_le_exp.mpr hexponent
    _ = (1 / ε) ^ (C * (w : ℝ)) :=
      (Real.rpow_def_of_pos (show 0 < 1 / ε by positivity) (C * (w : ℝ))).symm
)

/-- A width-`w` DNF is `ε`-close to a junta on at most `(1/ε)^(Cw)` coordinates for an
absolute `C`. The sign encoding sends true to `-1`. [OD14, Cor. 9.30]

**Proof sketch.** Use the DNF Fourier-tail bound at degree `O(w log(1/ε))` and
the total-influence bound `I[f] ≤ 2w`. Apply low-influence concentration at noise
rate one third and absorb its polynomial influence factor and exponential degree
factor into a power of `1/ε`. Constant approximation covers large errors, and
zero total influence covers width-zero formulas. -/
theorem dnf_junta : ∃ C : ℝ, 0 < C ∧
    ∀ (n w : ℕ) (d : DNF n), d.width ≤ w → ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
      ∃ (J : Finset (Fin n)) (h : BooleanFunc n),
        (J.card : ℝ) ≤ (1 / ε) ^ (C * (w : ℝ)) ∧ isPmOne h ∧ KKL.IsJunta h J ∧
        ThresholdFunctions.IsClose (fun x => boolToSign (d.eval x)) h ε := (by
  classical
  obtain ⟨C, hC, hparameters⟩ := dnf_junta_parameters
  refine ⟨C, hC, ?_⟩
  intro n w d hw ε hε
  let f : BooleanFunc n := fun x => boolToSign (d.eval x)
  have hf : isPmOne f := by
    intro x
    cases hx : d.eval x <;> simp [f, boolToSign, hx]
  have hεpos : 0 < ε := hε.1
  by_cases heps : (1 / 2 : ℝ) ≤ ε
  · have hvariance : cubeVariance f ≤ 1 := by
      rw [cubeVariance_eq_sum_nonempty_fourier, ← parseval_pm_one f hf]
      apply Finset.sum_le_sum
      intro S _
      split_ifs
      · positivity
      · exact le_rfl
    obtain ⟨h, hh, hjunta, herror⟩ := exists_boolean_constant_approximation f hf
    refine ⟨∅, h, ?_, hh, hjunta, ?_⟩
    · simpa using
        (show (0 : ℝ) ≤ (1 / ε) ^ (C * (w : ℝ)) by positivity)
    · change ThresholdFunctions.disagreementProbability f h ≤ ε
      linarith only [herror, hvariance, heps]
  · have hInonneg : 0 ≤ totalInfluence f := by
      rw [totalInfluence_eq_sum_sq_deg]
      positivity
    have hIupper : totalInfluence f ≤ 2 * (w : ℝ) := by
      calc
        totalInfluence f ≤ 2 * (d.width : ℝ) :=
          dnf_totalInfluence_le_two_mul_width d
        _ ≤ 2 * (w : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hw) (by norm_num)
    by_cases hwzero : w = 0
    · have hIzero : totalInfluence f = 0 := by
        have hupper : totalInfluence f ≤ 0 := by
          simpa [hwzero] using hIupper
        linarith only [hInonneg, hupper]
      obtain ⟨A, _, hFriedgut⟩ := friedgut_junta
      obtain ⟨J, h, hcard, _, hh, hjunta, hclose⟩ :=
        hFriedgut n f hf ε hε
      refine ⟨J, h, ?_, hh, hjunta, hclose⟩
      simpa [hIzero, hwzero] using hcard
    · have hwpos : 0 < w := by omega
      obtain ⟨t, hdecay, hsize⟩ :=
        hparameters w hwpos ε ⟨hεpos, by linarith only [heps]⟩
      let k : ℕ := 120 * w * (t + 1)
      let J : Finset (Fin n) := KKL.influentialCoords f
        (if totalInfluence f = 0 then 1
          else ε ^ 2 / totalInfluence f ^ 2 / (9 : ℝ) ^ k)
      have htail : ThresholdFunctions.fourierWeightAbove k f ≤ ε :=
        (dnf_fourierWeightAbove_le_of_width d w hw hwpos t).trans hdecay
      obtain ⟨hcard, _, happroximation⟩ :=
        lowInfluence_fourierConcentration f hf ε hε k
      obtain ⟨_, h, hh, hjunta, hclose⟩ := happroximation htail
      refine ⟨J, h, ?_, hh, hjunta, hclose⟩
      calc
        (J.card : ℝ) ≤ totalInfluence f ^ 3 / ε ^ 2 * (9 : ℝ) ^ k := hcard
        _ ≤ (2 * (w : ℝ)) ^ 3 / ε ^ 2 * (9 : ℝ) ^ k := by
          have hcube := pow_le_pow_left₀ hInonneg hIupper 3
          have hscaled := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcube
              (show 0 ≤ (ε ^ 2)⁻¹ by positivity))
            (show 0 ≤ (9 : ℝ) ^ k by positivity)
          simpa only [div_eq_mul_inv] using hscaled
        _ ≤ (1 / ε) ^ (C * (w : ℝ)) := hsize
)


end BooleanAnalysis.Hypercontractivity
