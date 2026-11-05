/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.InformationTheory.Extractors

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical closeness of samplers and of distributions

The ch. 2–4 layer measures the distance between two samplers from uniform seeds by test sets
(`StatClose`, `Asymptotic/Sampling.lean`). The information-theory layer measures the distance
between two finite distributions by distinguishers (`EpsClose`,
`InformationTheory/Extractors.lean`).
On a finite sample space the two agree: two samplers are `δ`-close exactly when the laws they push
the uniform seed distribution to are `δ`-close. This closes duplication-ledger item DL-4.

## Main results

* `uprob_comp_eq_probTrue_map`: the probability that a test accepts a sample is its acceptance
  probability under the sampler's law.
* `statClose_iff_epsClose_map`: `StatClose X Y δ` iff `EpsClose δ` between the laws of `X`
  and `Y`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 181.1 (`ε`-closeness) and §2.4.2 (statistical closeness of samplers, the device of
  the ch. 2–4 layer's decision D10).
-/

namespace TCSlib.Cryptography

open Finset TCSlib.InformationTheory

variable {σ τ γ : Type*} [Fintype σ] [Fintype τ] [Nonempty σ] [Nonempty τ] [Fintype γ]
  [DecidableEq γ]

/-- The probability that the test `D` accepts `X s` for a uniform seed `s` is the acceptance
probability of `D` under the law of `X` (the uniform distribution pushed forward along `X`). -/
theorem uprob_comp_eq_probTrue_map (X : σ → γ) (D : γ → Bool) :
    uprob (fun s => D (X s) = true) = ((FinDist.uniform σ).map X).probTrue D := by
  rw [uprob_comp_eq_sum_map X (fun g => D g = true), FinDist.probTrue]

/-- **Statistical closeness of samplers is closeness of their laws:** on a finite sample space,
`StatClose X Y δ` (every test set moves by at most `δ`) holds exactly when the laws of `X` and
`Y` are `δ`-close as finite distributions (every distinguisher has advantage at most `δ`).
[PS10, Def 181.1]

**Proof sketch.** A distinguisher `D` is the test set `{g | D g = true}`, and a test set `T` is
the distinguisher `decide ∘ T`; in both directions `uprob_comp_eq_probTrue_map` turns the
probability over seeds into the acceptance probability under the law. -/
theorem statClose_iff_epsClose_map (X : σ → γ) (Y : τ → γ) (δ : ℝ) :
    StatClose X Y δ ↔ EpsClose δ ((FinDist.uniform σ).map X) ((FinDist.uniform τ).map Y) := by
  constructor
  · intro h D
    rw [← uprob_comp_eq_probTrue_map, ← uprob_comp_eq_probTrue_map]
    exact h fun g => D g = true
  · intro h T
    classical
    have hX : uprob (fun s => T (X s)) = uprob (fun s => decide (T (X s)) = true) := by simp
    have hY : uprob (fun t => T (Y t)) = uprob (fun t => decide (T (Y t)) = true) := by simp
    rw [hX, hY, uprob_comp_eq_probTrue_map X (fun g => decide (T g)),
      uprob_comp_eq_probTrue_map Y (fun g => decide (T g))]
    exact h _

end TCSlib.Cryptography
