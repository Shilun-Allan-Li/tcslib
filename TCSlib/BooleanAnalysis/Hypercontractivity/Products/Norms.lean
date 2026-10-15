/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Group.Indicator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite weighted norm bounds

## Main definitions

No new definitions are introduced.

## Main results

* `FiniteNorms.weighted_holder`: Hölder inequality for finite nonnegative weights.
* `FiniteNorms.weighted_tail_le_norm_div_rpow`: Markov's inequality for finite weights.
* `FiniteNorms.norm_le_of_pairing`: recover norm bounds from all weighted pairings.
* `FiniteNorms.selfAdjoint_contraction`: same-exponent contraction transfers
  between conjugate norms for self-adjoint operators.

A private signed-power calculation supplies the sharp dual witness.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Propositions 9.19 and 10.4 (proofs), and Theorems 9.23
  and 10.24 (proofs).
-/

namespace BooleanAnalysis.Hypercontractivity.FiniteNorms

/-- For every real exponent `q > 1` and real number `z`, the signed witness
`g = z * |z| ^ (q - 2)` satisfies `z * g = |z| ^ q` and
`|g| ^ (q / (q - 1)) = |z| ^ q`, including when `z` is zero or negative.
This scalar calculation isolates the Hölder equality witness in
[OD14, Prop. 9.19 (proof)].

**Proof sketch.** Treat zero separately. Otherwise the absolute value is
positive. Rewrite the squared factor as an absolute square and combine real
exponents to obtain the pairing identity. The absolute value of the witness
is the `(q - 1)`st power of the absolute value of `z`; multiplying by the
conjugate exponent gives the second identity. -/
private theorem signed_power_dual (q : ℝ) (hq : 1 < q) (z : ℝ) :
    let g : ℝ := z * |z| ^ (q - 2)
    z * g = |z| ^ q ∧ |g| ^ (q / (q - 1)) = |z| ^ q :=
  (by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  dsimp only
  by_cases hz : z = 0
  · subst z
    simp [Real.zero_rpow hq0, Real.zero_rpow (div_ne_zero hq0 hq1)]
  · have hzpos : 0 < |z| := abs_pos.mpr hz
    constructor
    · calc
        z * (z * |z| ^ (q - 2)) = |z| ^ (2 : ℝ) * |z| ^ (q - 2) := by
          rw [Real.rpow_two, sq_abs, pow_two]
          ring
        _ = |z| ^ (2 + (q - 2)) := (Real.rpow_add hzpos 2 (q - 2)).symm
        _ = |z| ^ q := by congr 1; ring
    · have habs : |z * |z| ^ (q - 2)| = |z| ^ (q - 1) := by
        calc
          |z * |z| ^ (q - 2)| = |z| ^ (1 : ℝ) * |z| ^ (q - 2) := by
            rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg z) _),
              Real.rpow_one]
          _ = |z| ^ (1 + (q - 2)) := (Real.rpow_add hzpos 1 (q - 2)).symm
          _ = |z| ^ (q - 1) := by congr 1; ring
      rw [habs, ← Real.rpow_mul (abs_nonneg z)]
      congr 1
      rw [← mul_div_assoc, mul_div_cancel_left₀ q hq1]
)

open scoped BigOperators

/-- For conjugate real exponents greater than one, the weighted pairing of two
real functions on a finite set is bounded by the product of their weighted
norms. All weights are nonnegative; zero weights and arbitrary total weight
are permitted. This finite weighted formulation supplies the Hölder step in
[OD14, Prop. 9.19 (proof)].

**Proof sketch.** Bound each signed product by its absolute value. Split each
weight into its reciprocal-exponent powers and apply the finite Hölder
inequality. Conjugacy makes the two weight powers multiply back to the
original weight, while raising each factor to its norm exponent recovers
the corresponding weighted moment. -/
theorem weighted_holder {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {p q : ℝ} (hpq : Real.HolderConjugate p q) (f g : ι → ℝ) :
    (∑ i, w i * f i * g i) ≤
      (∑ i, w i * |f i| ^ p) ^ (1 / p) *
        (∑ i, w i * |g i| ^ q) ^ (1 / q) :=
  (by
  classical
  have hinv : 1 / p + 1 / q = 1 := by
    simpa only [one_div] using hpq.inv_add_inv_eq_one
  have hweight (i : ι) : w i ^ (1 / p) * w i ^ (1 / q) = w i := by
    rw [← Real.rpow_add' (hw i) (show 1 / p + 1 / q ≠ 0 by rw [hinv]; norm_num),
      hinv, Real.rpow_one]
  have hpow (r : ℝ) (hr : r ≠ 0) (i : ι) (a : ℝ) :
      (w i ^ (1 / r) * |a|) ^ r = w i * |a| ^ r := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (abs_nonneg a),
      ← Real.rpow_mul (hw i), one_div_mul_cancel hr, Real.rpow_one]
  calc
    (∑ i, w i * f i * g i) ≤ ∑ i, w i * |f i| * |g i| := by
      apply Finset.sum_le_sum
      intro i _
      calc
        w i * f i * g i = w i * (f i * g i) := by ring
        _ ≤ w i * |f i * g i| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (hw i)
        _ = w i * |f i| * |g i| := by rw [abs_mul]; ring
    _ = ∑ i, (w i ^ (1 / p) * |f i|) * (w i ^ (1 / q) * |g i|) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        w i * |f i| * |g i| =
            (w i ^ (1 / p) * w i ^ (1 / q)) * |f i| * |g i| := by
          rw [hweight]
        _ = (w i ^ (1 / p) * |f i|) * (w i ^ (1 / q) * |g i|) := by ring
    _ ≤ (∑ i, (w i ^ (1 / p) * |f i|) ^ p) ^ (1 / p) *
        (∑ i, (w i ^ (1 / q) * |g i|) ^ q) ^ (1 / q) :=
      Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset ι) hpq
        (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (abs_nonneg _))
        (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (abs_nonneg _))
    _ = (∑ i, w i * |f i| ^ p) ^ (1 / p) *
        (∑ i, w i * |g i| ^ q) ^ (1 / q) := by
      simp_rw [hpow p hpq.ne_zero, hpow q hpq.symm.ne_zero]
)

/-- For an exponent `q > 1`, a real function has weighted `q` norm at most
`N` if its weighted pairing with every test function is bounded by `N` times
that test function's conjugate norm. The weights and `N` are nonnegative;
zero weights and arbitrary total weight are permitted.
This is the finite weighted norm-duality step in [OD14, Prop. 10.4 (proof)].

**Proof sketch.** Pair the function with its signed power witness. Both the
pairing and the witness's conjugate moment equal the function's `q`th
moment. The assumed pairing bound then bounds that moment by `N` times its
conjugate root. For a positive moment, cancel this root to obtain the norm
bound. For a zero moment, use nonnegativity of `N`. -/
theorem norm_le_of_pairing {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (q : ℝ) (hq : 1 < q) (z : ι → ℝ) (N : ℝ) (hN : 0 ≤ N)
    (hpair : ∀ g : ι → ℝ,
      (∑ i, w i * z i * g i) ≤
        N * (∑ i, w i * |g i| ^ (q / (q - 1))) ^
          (1 / (q / (q - 1)))) :
    (∑ i, w i * |z i| ^ q) ^ (1 / q) ≤ N :=
  (by
  classical
  let r : ℝ := q / (q - 1)
  let g : ι → ℝ := fun i => z i * |z i| ^ (q - 2)
  let M : ℝ := ∑ i, w i * |z i| ^ q
  have hconj : Real.HolderConjugate q r :=
    (Real.holderConjugate_iff_eq_conjExponent hq).2 rfl
  have hMnonneg : 0 ≤ M :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _)
  have hpair_eq : (∑ i, w i * z i * g i) = M := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc]
    congr 1
    exact (signed_power_dual q hq (z i)).1
  have hmoment_eq : (∑ i, w i * |g i| ^ r) = M := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (signed_power_dual q hq (z i)).2
  have hbound : M ≤ N * M ^ (1 / r) := by
    have h := hpair g
    change (∑ i, w i * z i * g i) ≤ N * (∑ i, w i * |g i| ^ r) ^ (1 / r) at h
    simpa only [hpair_eq, hmoment_eq] using h
  change M ^ (1 / q) ≤ N
  by_cases hMzero : M = 0
  · rw [hMzero, Real.zero_rpow (one_div_ne_zero (by linarith : q ≠ 0))]
    exact hN
  · have hMpos : 0 < M := lt_of_le_of_ne hMnonneg (Ne.symm hMzero)
    apply le_of_mul_le_mul_right
      (a := M ^ (1 / r)) ?_ (Real.rpow_pos_of_pos hMpos _)
    calc
      M ^ (1 / q) * M ^ (1 / r) = M := by
        rw [← Real.rpow_add hMpos,
          show 1 / q + 1 / r = 1 by
            simpa only [one_div] using hconj.inv_add_inv_eq_one,
          Real.rpow_one]
      _ ≤ N * M ^ (1 / r) := hbound
)

/-- For an exponent `q > 1`, a self-adjoint operator on a finite weighted
real function space is contractive in the weighted `q` norm whenever it is
contractive in the conjugate norm. Weights may vanish and need not sum to one.
This is the finite weighted form of the operator duality argument in
[OD14, Prop. 9.19 (proof)], specialized to equal input and output exponents.

**Proof sketch.** Apply weighted norm duality to the transformed function.
Move the operator across each pairing by self-adjointness, apply weighted
Hölder, and use the assumed conjugate contraction to bound the resulting
test-function norm. -/
theorem selfAdjoint_contraction {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (T : (ι → ℝ) → ι → ℝ)
    (hself : ∀ f g : ι → ℝ,
      (∑ i, w i * T f i * g i) = ∑ i, w i * f i * T g i)
    (q : ℝ) (hq : 1 < q)
    (hcontract : ∀ g : ι → ℝ,
      (∑ i, w i * |T g i| ^ (q / (q - 1))) ^ (1 / (q / (q - 1))) ≤
        (∑ i, w i * |g i| ^ (q / (q - 1))) ^ (1 / (q / (q - 1)))) :
    ∀ f : ι → ℝ,
      (∑ i, w i * |T f i| ^ q) ^ (1 / q) ≤
        (∑ i, w i * |f i| ^ q) ^ (1 / q) :=
  (by
  classical
  intro f
  have hN :
      0 ≤ (∑ i, w i * |f i| ^ q) ^ (1 / q) :=
    Real.rpow_nonneg
      (Finset.sum_nonneg fun i _ =>
        mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _)) _
  refine norm_le_of_pairing w hw q hq (T f) _ hN ?_
  intro g
  rw [hself f g]
  have hconj : Real.HolderConjugate q (q / (q - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hq).2 rfl
  exact (weighted_holder w hw hconj f (T g)).trans
    (mul_le_mul_of_nonneg_left (hcontract g) hN)
)

/-- For nonnegative finite weights, the weight of the event `c ≤ |f|`
is at most the `q`-moment norm divided by `c`, raised to `q`, whenever
`q` and `c` are positive. [OD14, Thm. 9.23 (proof);
Thm. 10.24 (proof)]

**Proof sketch.** Pointwise, the event indicator is bounded by
`(|f| / c) ^ q`. Multiply by the nonnegative weights and sum.
Factor out `c ^ q` and rewrite the moment as the `q`th power of its
`1 / q` power. -/
lemma weighted_tail_le_norm_div_rpow {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (f : α → ℝ)
    (q c : ℝ) (hq : 0 < q) (hc : 0 < c) :
    (∑ x, w x *
      Set.indicator {x | c ≤ |f x|} (fun _ => (1 : ℝ)) x) ≤
      ((∑ x, w x * |f x| ^ q) ^ (1 / q) / c) ^ q :=
  (by
  classical
  have hmoment : 0 ≤ ∑ x, w x * |f x| ^ q :=
    Finset.sum_nonneg fun x _ =>
      mul_nonneg (hw x) (Real.rpow_nonneg (abs_nonneg _) _)
  rw [Real.div_rpow (Real.rpow_nonneg hmoment _) hc.le,
    ← Real.rpow_mul hmoment, one_div_mul_cancel hq.ne', Real.rpow_one]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hc q)).mpr
  calc
    (∑ x, w x * Set.indicator {x | c ≤ |f x|} (fun _ => (1 : ℝ)) x) * c ^ q =
        ∑ x, w x * (c ^ q *
          Set.indicator {x | c ≤ |f x|} (fun _ => (1 : ℝ)) x) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ x, w x * |f x| ^ q := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hw x)
      by_cases hx : c ≤ |f x|
      · rw [Set.indicator_of_mem (show x ∈ {x | c ≤ |f x|} from hx), mul_one]
        exact Real.rpow_le_rpow hc.le hx hq.le
      · rw [Set.indicator_of_notMem (show x ∉ {x | c ≤ |f x|} from hx), mul_zero]
        exact Real.rpow_nonneg (abs_nonneg _) _
)



/-- For nonnegative finite weights, a real function with weighted mean zero
has squared weighted absolute sum at most four times its weighted second
moment times the weight of its positive support.
This weighted formulation needs no normalization of the weights.
[OD14, Thm. 9.24 (proof); Thm. 10.23 (proof)]

**Proof sketch.** Zero mean makes the weighted absolute sum twice the
weighted positive-part sum. Apply weighted Cauchy–Schwarz to the function
restricted to its positive support, and bound its restricted second moment
by the full second moment. -/
theorem centered_abs_sum_sq_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (g : ι → ℝ)
    (hmean : (∑ i, w i * g i) = 0) :
    (∑ i, w i * |g i|) ^ 2 ≤
      4 * (∑ i, w i * g i ^ 2) *
        (∑ i, w i * (if 0 < g i then (1 : ℝ) else 0)) :=
  (by
  classical
  let I : ι → ℝ := fun i => if 0 < g i then 1 else 0
  have habs :
      (∑ i, w i * |g i|) = 2 * (∑ i, w i * g i * I i) := by
    calc
      _ = ∑ i, (2 * (w i * g i * I i) - w i * g i) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : 0 < g i
        · simp only [I, if_pos hi, mul_one, abs_of_pos hi]
          ring
        · simp [I, hi, abs_of_nonpos (le_of_not_gt hi), mul_neg]
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hmean, sub_zero]
  have hCS :
      (∑ i, w i * g i * I i) ^ 2 ≤
        (∑ i, w i * g i ^ 2) * (∑ i, w i * I i) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      (s := Finset.univ) (r := fun i => w i * g i * I i)
      (f := fun i => w i * g i ^ 2) (g := fun i => w i * I i)
    · intro i _
      exact mul_nonneg (hw i) (sq_nonneg _)
    · intro i _
      by_cases hi : 0 < g i
      · simpa [I, hi] using hw i
      · simp [I, hi]
    · intro i _
      by_cases hi : 0 < g i <;> simp [I, hi]
      ring
  rw [habs]
  change (2 * (∑ i, w i * g i * I i)) ^ 2 ≤
    4 * (∑ i, w i * g i ^ 2) * (∑ i, w i * I i)
  nlinarith [hCS]
)


/-- For nonnegative finite weights of positive total weight and any
positive base, the exponential of the weighted mean is at most the
weighted mean of the exponentials.
This unnormalized form permits arbitrary real exponents and bases above
or below one. [OD14, §10.3, KKL Isoperimetric Theorem (proof)]

**Proof sketch.** Apply Jensen's inequality to the convex function
`x ↦ ρ ^ x`, using the weights divided by their positive sum.
Multiply the resulting inequality by the total weight. -/
theorem weighted_rpow_mean_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : 0 < ∑ i, w i) (d : ι → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (∑ i, w i) * ρ ^ ((∑ i, w i * d i) / (∑ i, w i)) ≤
      ∑ i, w i * ρ ^ d i :=
  (by
  have h := (convexOn_rpow_left hρ).map_centerMass_le
    (t := Finset.univ) (w := w) (p := d)
    (fun i _ => hw i) hsum (fun i _ => Set.mem_univ (d i))
  simp only [Finset.centerMass, smul_eq_mul, Function.comp_apply,
    inv_mul_eq_div] at h
  calc
    _ = ρ ^ ((∑ i, w i * d i) / (∑ i, w i)) * (∑ i, w i) := mul_comm _ _
    _ ≤ _ := (le_div_iff₀ hsum).mp h
)


/-- If nonnegative numbers have positive sum and the sum of their
three-halves powers is at least a nonnegative `A`, one of the numbers
is at least the square of the ratio of `A` to their sum.
[OD14, §10.3, KKL Isoperimetric Theorem (proof), equation (10.7)]

**Proof sketch.** Choose a largest number; positive total sum ensures
the index type is nonempty. Write each three-halves power as the number
times its square root and bound the square root by that of the maximum.
Sum, divide by the positive total, and square the resulting inequality. -/
theorem exists_sq_div_sum_le_of_sum_three_halves {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hsum : 0 < ∑ i, a i) (A : ℝ) (hA : 0 ≤ A)
    (hbound : A ≤ ∑ i, a i ^ (3 / 2 : ℝ)) :
    ∃ i, (A / (∑ j, a j)) ^ 2 ≤ a i :=
  (by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    have heq := Finset.not_nonempty_iff_eq_empty.mp h
    rw [heq, Finset.sum_empty] at hsum
    exact lt_irrefl 0 hsum
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ a hne
  have hterm (j : ι) : a j ^ (3 / 2 : ℝ) ≤ a j * Real.sqrt (a i) := by
    calc
      _ = a j * Real.sqrt (a j) := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add_of_nonneg (ha j) zero_le_one (by norm_num),
          Real.rpow_one, ← Real.sqrt_eq_rpow]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hmax j (Finset.mem_univ j))) (ha j)
  have hroot : A / (∑ j, a j) ≤ Real.sqrt (a i) := by
    apply (div_le_iff₀ hsum).2
    calc
      A ≤ ∑ j, a j ^ (3 / 2 : ℝ) := hbound
      _ ≤ ∑ j, a j * Real.sqrt (a i) :=
        Finset.sum_le_sum fun j _ => hterm j
      _ = Real.sqrt (a i) * (∑ j, a j) := by
        rw [← Finset.sum_mul]
        exact mul_comm _ _
  refine ⟨i, ?_⟩
  simpa only [Real.sq_sqrt (ha i)] using
    pow_le_pow_left₀ (div_nonneg hA hsum.le) hroot 2
)

/-- For nonnegative subset weights and `0 ≤ ρ ≤ 1`, the omitted
degree-at-most-`k` weight multiplied by `ρ^k` is bounded by the sum,
over coordinates outside `J`, of their degree-weighted subset contributions.
[OD14, Thm. 9.28 (proof); §10.3, Friedgut's Junta Theorem]
This abstract finite-sum formulation includes `ρ = 0` and uses natural powers.

**Proof sketch.** Exchange the coordinate and subset sums on the right.
Every omitted subset of degree at most `k` contains a coordinate outside
`J`, whose contribution is `ρ^|S|` times the subset weight. Since
`0 ≤ ρ ≤ 1`, this contribution is at least `ρ^k` times that weight.
Bound it by the nonnegative coordinate sum using the single-term estimate,
then sum over subsets. All other contributions are nonnegative. -/
theorem weighted_lowDegree_omission_le {α : Type*}
    [Fintype α] [DecidableEq α]
    (E : Finset α → ℝ) (hE : ∀ S, 0 ≤ E S)
    (J : Finset α) (k : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ρ ^ k * (∑ S : Finset α,
      if S.card ≤ k ∧ ¬ S ⊆ J then E S else 0) ≤
      ∑ i : α, if i ∈ J then 0 else
        ∑ S : Finset α, if i ∈ S then ρ ^ S.card * E S else 0 :=
  (by
  classical
  calc
    ρ ^ k * (∑ S : Finset α,
        if S.card ≤ k ∧ ¬ S ⊆ J then E S else 0) =
        ∑ S : Finset α,
          ρ ^ k * (if S.card ≤ k ∧ ¬ S ⊆ J then E S else 0) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ S : Finset α, ∑ i : α,
        if i ∈ J then 0 else if i ∈ S then ρ ^ S.card * E S else 0 := by
      apply Finset.sum_le_sum
      intro S _
      have hES := hE S
      have hterm (i : α) :
          0 ≤ (if i ∈ J then 0 else
            if i ∈ S then ρ ^ S.card * E S else 0) := by
        split_ifs <;> positivity
      by_cases hS : S.card ≤ k ∧ ¬ S ⊆ J
      · rw [if_pos hS]
        obtain ⟨i, hiS, hiJ⟩ := Finset.not_subset.mp hS.2
        calc
          ρ ^ k * E S ≤ ρ ^ S.card * E S :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_of_le_one hρ hρ1 hS.1) hES
          _ = (if i ∈ J then 0 else
              if i ∈ S then ρ ^ S.card * E S else 0) := by
            simp [hiJ, hiS]
          _ ≤ ∑ i : α, if i ∈ J then 0 else
              if i ∈ S then ρ ^ S.card * E S else 0 :=
            Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
      · rw [if_neg hS, mul_zero]
        exact Finset.sum_nonneg fun i _ => hterm i
    _ = ∑ i : α, if i ∈ J then 0 else
        ∑ S : Finset α, if i ∈ S then ρ ^ S.card * E S else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ J <;> simp [hi]
)

end BooleanAnalysis.Hypercontractivity.FiniteNorms
