/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.InformationTheory.StatisticalDistance

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concrete security experiments

The concrete layer fixes one value of the security parameter and quantifies over all
adversaries, given as functions of their input and of a uniformly random coin string
from a finite type `ρ`. No running time is imposed here; efficiency is the job of the
asymptotic layer. The experiments are:

* inversion: on `f x` for uniform `x`, output some preimage of `f x`;
* prediction: on `f x`, output the bit `B x`;
* distinguishing: tell apart samples `X s` and `Y t` from uniform seeds `s` and `t`.

Samplers `X : σ → γ` from a finite seed type `σ` describe exactly the distributions
that are pushforwards of uniform coins, which covers every efficiently samplable
ensemble at a fixed parameter.

## Main definitions

* `invProb f A`: the probability that `A` inverts `f`.
* `predProb f B A`: the probability that `A` predicts `B` from `f`.
* `acceptProb X D`: the probability that `D` accepts a sample of `X`.
* `distAdv X Y D`: the distinguishing advantage of `D` between `X` and `Y`.

## Main results

* `abs_sum_sub_le_statDist`: a test set distinguishes two distributions by at most
  their statistical distance.
* `distAdv_le_statDist`: the distinguishing advantage of any distinguisher is at most
  the statistical distance of the sampled distributions.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (inversion), Definition 2.3 (prediction),
  Definitions 3.2–3.4 and Lemma 3.1 (distinguishing).
-/

namespace TCSlib.Cryptography

open Finset TCSlib.InformationTheory

variable {α β ρ σ τ γ : Type*} [Fintype α] [Fintype ρ] [Fintype σ] [Fintype τ]

/-- The probability that the adversary `A`, given `f x` for uniform `x` and uniform coins
`r`, outputs a preimage of `f x`. [Gar26, Definition 2.1, Equation (2.1)], at one value of
the security parameter; the input `1^n` is implicit in the fixed types. -/
noncomputable def invProb (f : α → β) (A : β → ρ → α) : ℝ :=
  uprob fun z : α × ρ => f (A (f z.1) z.2) = f z.1

/-- The probability that the adversary `A`, given `f x` for uniform `x` and uniform coins
`r`, outputs the bit `B x`. [Gar26, Definition 2.3], at one value of the security
parameter. -/
noncomputable def predProb (f : α → β) (B : α → Bool) (A : β → ρ → Bool) : ℝ :=
  uprob fun z : α × ρ => A (f z.1) z.2 = B z.1

/-- The probability that the distinguisher `D` with uniform coins accepts a sample `X s`
for a uniform seed `s`. [Gar26, Definitions 3.2 and 3.4], the quantities `p(n)` and
`q(n)`. -/
noncomputable def acceptProb (X : σ → γ) (D : γ → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => D (X z.1) z.2 = true

/-- The distinguishing advantage of `D` between the sampled distributions `X` and `Y`,
`|Pr[D(X) = 1] - Pr[D(Y) = 1]|`. [Gar26, Definitions 3.2 and 3.4], the quantity
`Δ_A(n)`. -/
noncomputable def distAdv (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) : ℝ :=
  |acceptProb X D - acceptProb Y D|

/-- The probability that a uniform seed `s` has `X s` in an event `q` is the mass of `q` under
the pushforward of the uniform distribution along `X`. Technical glue between `uprob` and
`FinDist.map`.

**Proof sketch.** Both sides equal `∑ s, [q (X s)] / |σ|`: on the right, group the seeds
by their image under `X`. -/
theorem uprob_comp_eq_sum_map [Nonempty σ] [Fintype γ] [DecidableEq γ] (X : σ → γ)
    (q : γ → Prop) [DecidablePred q] :
    uprob (fun s => q (X s)) = ∑ g ∈ univ.filter q, (FinDist.uniform σ).map X g := by
  rw [uprob_eq_card_filter, sum_filter]
  have h := Finset.sum_fiberwise' univ X
    (fun g => if q g then (Fintype.card σ : ℝ)⁻¹ else 0)
  have h2 : ∑ s, (if q (X s) then (Fintype.card σ : ℝ)⁻¹ else 0) =
      ((univ.filter fun s => q (X s)).card : ℝ) / Fintype.card σ := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [← h2, ← h]
  refine sum_congr rfl fun g _ => ?_
  split_ifs <;> simp [FinDist.map_apply]

/-- The acceptance probability of `D` on samples of `X` is the average over the coins `r` of
the mass, under the distribution of `X`, of the set of samples that `D` accepts with coins
`r`. Technical glue for `distAdv_le_statDist`.

**Proof sketch.** Swap the two coordinates of the sample space, apply Fubini
(`uprob_prod`) to average over the coins first, and rewrite each section with
`uprob_comp_eq_sum_map`. -/
theorem acceptProb_eq_uexp_sum_map [Nonempty σ] [Fintype γ] [DecidableEq γ] (X : σ → γ)
    (D : γ → ρ → Bool) :
    acceptProb X D = uexp (fun r : ρ => ∑ g ∈ univ.filter (fun g => D g r = true),
        (FinDist.uniform σ).map X g) := by
  rw [acceptProb, ← uprob_comp_equiv (Equiv.prodComm ρ σ), uprob_prod]
  congr 1
  funext r
  exact uprob_comp_eq_sum_map X (fun g => D g r = true)

/-- For any set `T` of outcomes, `|p(T) - q(T)|` is at most the statistical distance of `p`
and `q`. This is the deterministic case of [Gar26, Lemma 3.1].

**Proof sketch.** The differences `d = p - q` sum to zero, so the sum of `d` over the
complement of `T` is `-d(T)`. Splitting `∑ |d|` over `T` and its complement and applying
the triangle inequality to each part gives `∑ |d| ≥ 2 |d(T)|`. -/
theorem abs_sum_sub_le_statDist [Fintype γ] (p q : FinDist γ) (T : Finset γ) :
    |∑ g ∈ T, (p g - q g)| ≤ statDist p q := by
  classical
  have h0 : ∑ g, (p g - q g) = 0 := by
    rw [sum_sub_distrib, p.sum_prob, q.sum_prob, sub_self]
  have hsplit := sum_add_sum_compl T (fun g => p g - q g)
  have habs := sum_add_sum_compl T (fun g => |p g - q g|)
  have h1 := abs_sum_le_sum_abs (fun g => p g - q g) T
  have h2 := abs_sum_le_sum_abs (fun g => p g - q g) Tᶜ
  have hneg : ∑ g ∈ Tᶜ, (p g - q g) = -∑ g ∈ T, (p g - q g) := by linarith
  rw [hneg, abs_neg] at h2
  rw [statDist]
  linarith

/-- The distinguishing advantage of any distinguisher, deterministic or with coins, is at
most the statistical distance of the two sampled distributions. [Gar26, Lemma 3.1].

**Proof sketch.** Average over the coins (`acceptProb_eq_uexp_sum_map`): for fixed coins
`r` the distinguisher is a test set `T_r`, whose advantage is `|X(T_r) - Y(T_r)|`. By
`abs_sum_sub_le_statDist` each of these is at most the statistical distance, and the
absolute value of an average is at most the average of the absolute values. -/
theorem distAdv_le_statDist [Nonempty σ] [Nonempty τ] [Nonempty ρ] [Fintype γ]
    [DecidableEq γ] (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
    distAdv X Y D ≤
      statDist ((FinDist.uniform σ).map X) ((FinDist.uniform τ).map Y) := by
  have hρ : (0 : ℝ) < Fintype.card ρ := Nat.cast_pos.2 Fintype.card_pos
  rw [distAdv, acceptProb_eq_uexp_sum_map X, acceptProb_eq_uexp_sum_map Y, uexp, uexp,
    ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_comm, ← nsmul_eq_mul, ← card_univ, ← sum_const]
  refine sum_le_sum fun r _ => ?_
  rw [← sum_sub_distrib]
  exact abs_sum_sub_le_statDist _ _ _

end TCSlib.Cryptography
