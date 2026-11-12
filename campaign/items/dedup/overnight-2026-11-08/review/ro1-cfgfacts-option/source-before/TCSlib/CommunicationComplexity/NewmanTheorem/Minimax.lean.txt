/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinComplexity
import TCSlib.CommunicationComplexity.NewmanTheorem.Comparison
import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Minimax Principle for Public-Coin Communication Complexity

## Main definitions

- `Deterministic.Protocol.distributionalError`: the probability, under a distribution `μ`
  on `X × Y`, that a deterministic protocol's output disagrees with `f`

## Main results

- `PublicCoin.lt_communicationComplexity_of_forall_distributionalError_gt`: Yao's minimax
  principle: if every deterministic protocol of complexity ≤ n fails with probability > ε
  under some distribution μ, then the public-coin randomized CC of f at error ε is > n.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016;
  arXiv:1509.06257.
* [Yao77] A. C.-C. Yao, "Probabilistic computations: toward a unified measure of
  complexity", *FOCS 1977*, pp. 222–227.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory

namespace Deterministic

namespace Protocol

variable {X Y α : Type*}

/-- The distributional error of a deterministic protocol with respect
to a distribution `μ` on `X × Y`: the probability, for an input `(x, y)` drawn from `μ`,
that the protocol's output disagrees with `f x y`.
[RY20, Ch. 3, §Variants of Randomized Protocols: average-case error e w.r.t. µ]. -/
noncomputable def distributionalError
    (p : Protocol X Y α)
    (μ : FiniteProbabilitySpace (X × Y))
    (f : X → Y → α) : ℝ := by
  letI := μ
  exact volume.real {xy : X × Y | p.run xy.1 xy.2 ≠ f xy.1 xy.2}

end Protocol

end Deterministic

namespace PublicCoin

/-- Fubini for the failure event of a public-coin protocol: averaging over the coin tape
the `μ`-probability that the protocol fails equals averaging over inputs (under `μ`) the
probability over the coin tape that the protocol fails.

**Proof sketch.** Write each inner probability as the integral of the failure indicator
on a finite space, so both sides are iterated integrals of the same indicator on
`CoinTape m × (X × Y)`; then swap the order of integration. -/
private lemma failureIntegral_swap
    {X Y α : Type*} {m : ℕ} [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol (CoinTape m) X Y α)
    (f : X → Y → α) :
    ∫ ω, volume.real {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2} =
      ∫ xy : X × Y, volume.real {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2} := by
  -- Rewrite each probability as an integral of the corresponding failure indicator,
  -- then swap the order of integration.
  have hg_eq : ∀ ω, volume.real {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2} =
      ∫ xy : X × Y,
        Set.indicator {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
          (fun _ => (1 : ℝ)) xy := by
    intro ω
    apply FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
  have hh_eq : ∀ xy : X × Y,
      volume.real {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2} =
        ∫ ω : CoinTape m,
          Set.indicator {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
            (fun _ => (1 : ℝ)) ω := by
    intro xy
    apply FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
  simp_rw [hg_eq, hh_eq]
  simpa [Set.indicator_apply] using
    (MeasureTheory.integral_integral_swap (Integrable.of_finite) :
      ∫ xy : X × Y, ∫ ω : CoinTape m,
        Set.indicator {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
          (fun _ => (1 : ℝ)) ω =
      ∫ ω : CoinTape m, ∫ xy : X × Y,
        Set.indicator {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
          (fun _ => (1 : ℝ)) xy).symm

open Classical in
/-- Yao's minimax principle (the easy direction): if there is a distribution `μ` on
`X × Y` such that every deterministic protocol of complexity at most `n` has
distributional error greater than `ε` under `μ`, then the public-coin randomized
communication complexity of `f` at error `ε` is greater than `n`.
[RY20, Thm 3.3] (easy direction) / [Rou16, Lemma 4.10]; historically [Yao77].
Deviation: stated in the strict form `n < R^pub_ε(f)` from "every `n`-bit deterministic
protocol errs with probability `> ε` under `μ`", rather than as the equality of the
worst-case and the maximal distributional complexities.

**Proof sketch.** Step 1: argue by contradiction: if the public-coin complexity were at
most `n`, there would be a public-coin protocol `p` on some coin tape with complexity at
most `n` and worst-case error at most `ε`. Step 2: for every fixed coin tape `ω`, the
deterministic protocol obtained by fixing the coins of `p` has complexity at most `n`,
so by hypothesis its failure probability `g(ω)` under `μ` exceeds `ε`; hence the average
of `g` over the coin tape exceeds `ε`. Step 3: for every fixed input `(x, y)`, the failure
probability `h(x, y)` over the coin tape is at most `ε`, so the average of `h` under `μ`
is at most `ε`. Step 4: by Fubini (`failureIntegral_swap`) the two averages are equal,
a contradiction. -/
theorem lt_communicationComplexity_of_forall_distributionalError_gt
    {X Y α : Type*}
    (f : X → Y → α) (ε : ℝ) (n : ℕ)
    (μ : FiniteProbabilitySpace (X × Y))
    (h : ∀ (p : Deterministic.Protocol X Y α),
      p.complexity ≤ n →
      p.distributionalError μ f > ε) :
    n < communicationComplexity f ε := by
  -- Step 1: prove by contradiction: suppose CC(f, ε) ≤ n
  rw [show (n : ENat) < communicationComplexity f ε ↔
    ¬(communicationComplexity f ε ≤ n) from not_le.symm]
  intro hle
  -- Get a randomized protocol p with complexity ≤ n and error ≤ ε
  obtain ⟨m, p, hp, hc⟩ := (communicationComplexity_le_iff f ε n).mp hle
  -- Step 2: by h, each p.toDeterministic ω has failure prob > ε under μ
  have hdet_fail : ∀ ω : CoinTape m,
      volume.real {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2} > ε := by
    intro ω
    have h1 := h (p.toDeterministic ω) (by simp [hc])
    simpa [Deterministic.Protocol.distributionalError, Protocol.toDeterministic_run] using h1
  -- Use μ as the ambient finite probability space on X × Y.
  letI : FiniteProbabilitySpace (X × Y) := μ
  -- g(ω) = vol_μ({(x,y) | p fails with randomness ω}), satisfies g(ω) > ε
  set g : CoinTape m → ℝ := fun ω =>
    volume.real {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
  have hg_gt : ∀ ω, ε < g ω := hdet_fail
  -- Step 3: h(x,y) = vol_CoinTape({ω | p fails on (x,y)}), satisfies h(x,y) ≤ ε
  set h' : X × Y → ℝ := fun xy =>
    volume.real {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
  have hh_le : ∀ xy : X × Y, h' xy ≤ ε := fun ⟨x, y⟩ => hp x y
  -- Lower bound: ∫_ω g(ω) > ε (since g > ε pointwise)
  have h_lower : ε < ∫ ω, g ω :=
    FiniteProbabilitySpace.lt_integral_of_lt hg_gt
  -- Upper bound: ∫_{(x,y)} h(x,y) ≤ ε (since h ≤ ε pointwise)
  have h_upper : ∫ xy : X × Y, h' xy ≤ ε :=
    FiniteProbabilitySpace.integral_le_of_le hh_le
  -- Step 4: Fubini: average first over randomness or first over inputs.
  have h_fubini : ∫ ω, g ω = ∫ xy : X × Y, h' xy := by
    simpa [g, h'] using failureIntegral_swap (p := p) (f := f)
  linarith

end PublicCoin

end CommunicationComplexity
