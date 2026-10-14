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

/-- The distinguishing advantage of any distinguisher, deterministic or with coins, is at
most the statistical distance of the two sampled distributions. [Gar26, Lemma 3.1].

**Proof sketch.** Average over the coins: for fixed coins the distinguisher is a
test set `T`, whose advantage is `|X(T) - Y(T)|`. This is at most the sum of the
positive parts of `X - Y`, which is the statistical distance. -/
theorem distAdv_le_statDist [Nonempty σ] [Nonempty τ] [Nonempty ρ] [Fintype γ]
    [DecidableEq γ] (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
    distAdv X Y D ≤
      statDist ((FinDist.uniform σ).map X) ((FinDist.uniform τ).map Y) := by
  sorry

end TCSlib.Cryptography
