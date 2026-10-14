/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary
import Mathlib.Data.Fintype.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Keyed function families, random functions and the PRF advantage

At one fixed value of the security parameter, a function ensemble [Gar26, Definition 3.6]
is a random variable ranging over functions `I → O`. Following the concrete-layer
convention, random variables are pushforwards of uniform seeds, so an efficiently
computable ensemble [Gar26, Definition 3.8] is a *keyed family* `F : K → I → O`, sampled
by drawing a uniform key `k : K` and outputting `F k`. The random function ensemble
[Gar26, Definition 3.7] is the uniform distribution on the finite type `I → O`, sampled
by the identity.

The PRF advantage of an oracle adversary `A` [Gar26, Definition 3.9] is
`|Pr_{k,r}[A^{F_k}(r) = 1] - Pr_{R,r}[A^R(r) = 1]|`. It is the distinguishing advantage
`distAdv` of the oracle adversary viewed as a distinguisher of whole functions; the
adversary only ever sees the values at its queries, which is what makes the advantage
meaningful for bounded-query adversaries.

The efficiency conditions of Definition 3.8 (a polynomial-time key generator and
evaluator) and the quantification over non-uniform PPT adversaries of Definition 3.9
belong to the asymptotic layer; here the only resource tracked is the query bound
`OracleAdversary.BoundedBy`.

## Main definitions

* `randomFunction I O`: the sampler of a uniform random function `I → O`.
* `prfAdv F A`: the PRF advantage of the oracle adversary `A` against the keyed family `F`.

## Main results

* `prfAdv_eq`: the advantage written out as a difference of two probabilities.
* `acceptProb_comp_equiv`: reparametrizing a sampler's seed by a bijection does not change
  acceptance probabilities.
* `prfAdv_nonneg`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.1, Definitions 3.6–3.9.
-/

namespace TCSlib.Cryptography

variable {K I O ρ σ σ' γ : Type*}

/-- The sampler of a uniformly random function `I → O`: the seed is the function table
itself, a uniform element of the finite type `I → O`. This is the random function
ensemble `R_n` of [Gar26, Definition 3.7] at one value of the security parameter; its
seed has `|I| · log |O|` bits, `n · 2^n` for `I = O = {0,1}^n`. -/
def randomFunction (I O : Type*) : (I → O) → I → O := id

/-- The PRF advantage of the oracle adversary `A` against the keyed function family
`F : K → I → O` (a function ensemble [Gar26, Definitions 3.6 and 3.8], keys uniform in
`K`): `|Pr_{k,r}[A^{F_k}(r) = 1] - Pr_{R,r}[A^R(r) = 1]|` with `R` a uniform random
function, [Gar26, Definition 3.9] at one value of the security parameter. `F` is
pseudorandom when this is negligible for every efficient adversary; the concrete layer
bounds it by explicit reductions instead. -/
noncomputable def prfAdv [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) : ℝ :=
  distAdv F (randomFunction I O) (oracleDist A)

/-- The PRF advantage written out: the difference between the probability that `A`
accepts with oracle `F k` for uniform `k` and coins `r`, and the probability that it
accepts with a uniform random function `R` as oracle. [Gar26, Definition 3.9]. -/
theorem prfAdv_eq [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) :
    prfAdv F A = |uprob (fun z : K × ρ => (A z.2).eval (F z.1) = true) -
      uprob (fun z : (I → O) × ρ => (A z.2).eval z.1 = true)| := rfl

/-- The PRF advantage is nonnegative. -/
theorem prfAdv_nonneg [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) : 0 ≤ prfAdv F A :=
  abs_nonneg _

/-- Reparametrizing the seed of a sampler by a bijection does not change the probability
that a distinguisher accepts: if `e : σ' ≃ σ` then `X ∘ e` and `X` define the same
distribution. -/
theorem acceptProb_comp_equiv [Fintype σ] [Fintype σ'] [Fintype ρ] (e : σ' ≃ σ)
    (X : σ → γ) (D : γ → ρ → Bool) : acceptProb (X ∘ e) D = acceptProb X D :=
  uprob_comp_equiv (e.prodCongr (Equiv.refl ρ)) (fun z : σ × ρ => D (X z.1) z.2 = true)

/-- Two samplers producing the same sample from every seed have the same acceptance
probability. -/
theorem acceptProb_congr [Fintype σ] [Fintype ρ] {X Y : σ → γ} (h : ∀ s, X s = Y s)
    (D : γ → ρ → Bool) : acceptProb X D = acceptProb Y D := by
  rw [funext h]

end TCSlib.Cryptography
