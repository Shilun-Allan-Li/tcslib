/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinOneWay
import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Minimax Principle for One-Way Public-Coin Protocols

## Main definitions

- `Deterministic.OneWay.Protocol.distributionalError`: the probability, under a
  distribution `μ` on `X × Y`, that a deterministic one-way protocol's output disagrees
  with `f`
- `PublicCoin.OneWay.Protocol.toDeterministic`: the deterministic one-way protocol
  obtained by fixing the public randomness

## Main results

- `PublicCoin.OneWay.lt_communicationComplexity_of_forall_distributionalError_gt`: Yao's
  minimax principle for one-way protocols — if every deterministic one-way protocol of
  cost ≤ n has distributional error > ε under some joint distribution, then the one-way
  public-coin complexity at error ε exceeds n.

## References

* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016;
  arXiv:1509.06257.
* [Yao77] A. C.-C. Yao, "Probabilistic computations: toward a unified measure of
  complexity", *FOCS 1977*, pp. 222–227.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory

namespace Deterministic
namespace OneWay
namespace Protocol

variable {X Y α : Type*}

/-- The distributional error of a deterministic one-way protocol with respect
to a distribution `μ` on `X × Y`: the probability, for an input `(x, y)` drawn from `μ`,
that the protocol's output disagrees with `f x y`. [Rou16, Lemma 2.3] (the
distributional error of a deterministic one-way protocol). -/
noncomputable def distributionalError
    (p : Protocol X Y α)
    (μ : FiniteProbabilitySpace (X × Y))
    (f : X → Y → α) : ℝ := by
  letI := μ
  exact (volume {xy : X × Y | p.run xy.1 xy.2 ≠ f xy.1 xy.2}).toReal

end Protocol
end OneWay
end Deterministic

namespace PublicCoin
namespace OneWay
namespace Protocol

variable {Ω X Y α : Type*}

/-- Fix the public randomness `ω` in a one-way public-coin protocol,
producing a deterministic one-way protocol. -/
def toDeterministic (p : Protocol Ω X Y α) (ω : Ω) :
    Deterministic.OneWay.Protocol X Y α where
  Message := p.Message
  send := fun x => p.send (ω, x)
  decode := fun m y => p.decode m (ω, y)

/-- Running the deterministic one-way protocol obtained by fixing the randomness `ω` on
`(x, y)` gives the same output as running the public-coin protocol on `(x, y)` with
randomness `ω`. -/
@[simp] theorem toDeterministic_run (p : Protocol Ω X Y α) (ω : Ω) (x : X) (y : Y) :
    (p.toDeterministic ω).run x y = p.rrun x y ω := rfl

/-- Fixing the randomness of a one-way public-coin protocol does not change its cost
(the message alphabet is unchanged). -/
@[simp] theorem toDeterministic_cost (p : Protocol Ω X Y α) (ω : Ω) :
    (p.toDeterministic ω).cost = p.cost := rfl

end Protocol

/-- Fubini for the failure event of a one-way public-coin protocol: averaging over the
coin tape the `μ`-probability that the protocol fails equals averaging over inputs
(under `μ`) the probability over the coin tape that the protocol fails.

**Proof sketch.** Write each inner probability as the integral of the failure indicator
on a finite space, so both sides are iterated integrals of the same indicator on
`CoinTape m × (X × Y)`; then swap the order of integration. -/
private lemma failureIntegral_swap
    {X Y α : Type*} {m : ℕ} [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol (CoinTape m) X Y α)
    (f : X → Y → α) :
    ∫ ω, (volume {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal =
      ∫ xy : X × Y, (volume {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal := by
  have hg_eq : ∀ ω, (volume {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal =
      ∫ xy : X × Y,
        Set.indicator {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
          (fun _ => (1 : ℝ)) xy := by
    intro ω
    apply FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
  have hh_eq : ∀ xy : X × Y,
      (volume {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal =
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
/-- Yao's minimax principle (the easy direction) for one-way public-coin protocols:
if some joint distribution `μ` forces every deterministic one-way protocol of
cost at most `n` to have distributional error strictly greater than `ε`,
then the one-way public-coin communication complexity at error `ε` is greater than `n`.
[Rou16, Lemma 2.3]; historically [Yao77]. Deviation: stated in the strict form
`n < R^{pub,→}_ε(f)` from the hypothesis "every deterministic one-way protocol of cost
`≤ n` errs with probability `> ε` under `μ`" (the contrapositive of Rou16's hypothesis
"every deterministic one-way protocol with distributional error `≤ ε` has cost `≥ k`"),
as in `Minimax.lean`.

**Proof sketch.** Step 1: argue by contradiction: if the one-way public-coin complexity
were at most `n`, there would be a one-way public-coin protocol `p` on some coin tape
with cost at most `n` and worst-case error at most `ε`. Step 2: for every fixed coin tape
`ω`, fixing the coins of `p` gives a deterministic one-way protocol of cost at most `n`,
so by hypothesis its failure probability `g(ω)` under `μ` exceeds `ε`; hence the average
of `g` over the coin tape exceeds `ε`. Step 3: for every fixed input `(x, y)`, the failure
probability `h(x, y)` over the coin tape is at most `ε`, so the average of `h` under `μ`
is at most `ε`. Step 4: by Fubini (`failureIntegral_swap`) the two averages are equal,
a contradiction. -/
theorem lt_communicationComplexity_of_forall_distributionalError_gt
    {X Y α : Type*}
    (f : X → Y → α) (ε : ℝ) (n : ℕ)
    (μ : FiniteProbabilitySpace (X × Y))
    (h : ∀ (p : Deterministic.OneWay.Protocol X Y α),
      p.cost ≤ n →
      p.distributionalError μ f > ε) :
    n < communicationComplexity f ε := by
  -- Step 1: prove by contradiction: suppose CC(f, ε) ≤ n
  rw [show (n : ENat) < communicationComplexity f ε ↔
    ¬(communicationComplexity f ε ≤ n) from not_le.symm]
  intro hle
  obtain ⟨m, p, hp, hc⟩ := (communicationComplexity_le_iff f ε n).mp hle
  -- Step 2: each fixed-coin deterministic protocol has failure prob > ε under μ
  have hdet_fail : ∀ ω : CoinTape m,
      (volume {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal > ε := by
    intro ω
    have h1 := h (Protocol.toDeterministic p ω) (by simp [hc])
    simpa [Deterministic.OneWay.Protocol.distributionalError, Protocol.toDeterministic_run] using h1
  letI : FiniteProbabilitySpace (X × Y) := μ
  set g : CoinTape m → ℝ := fun ω =>
    (volume {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal
  have hg_gt : ∀ ω, ε < g ω := hdet_fail
  -- Step 3: for each input, the failure probability over the coin tape is ≤ ε
  set h' : X × Y → ℝ := fun xy =>
    (volume {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal
  have hh_le : ∀ xy : X × Y, h' xy ≤ ε := fun ⟨x, y⟩ => hp x y
  have h_lower : ε < ∫ ω, g ω :=
    FiniteProbabilitySpace.lt_integral_of_lt hg_gt
  have h_upper : ∫ xy : X × Y, h' xy ≤ ε :=
    FiniteProbabilitySpace.integral_le_of_le hh_le
  -- Step 4: Fubini: the two averages coincide
  have h_fubini : ∫ ω, g ω = ∫ xy : X × Y, h' xy := by
    simpa [g, h'] using failureIntegral_swap (p := p) (f := f)
  linarith

end OneWay
end PublicCoin

end CommunicationComplexity
