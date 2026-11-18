/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSimulator
import TCSlib.Cryptography.Foundations.Subexponential

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bounds for the exact rank correction

The actual unconditioned three-by-three rank correction is positive and bounded by 3/p.
Its average over public parameters obeys the same bound for every fixed prime schedule.
Exponential growth of the order makes this single statistical loss subexponentially small.

## Main definitions

This module introduces no algorithm, sampler, or additional security loss.

## Main results

* `Wee20.Linear.rankSlack_nonneg`, `rankSlack_le_three_div`: pointwise rank bounds.
* `Wee20.Linear.linearSlack_nonneg`, `linearSlack_le_fixedOrder`: averaged bounds.
* `Wee20.Linear.linearSlack_subexpSmall`, `linearSlack_negligible`: asymptotic consequences.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Section 4.2 and Appendix B,
  Theorem 1, p.12. The exact three-by-three failure replaces its printed 1/p estimate.
* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, 2026, Section 1.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

open Complexity TCSlib.Cryptography.Pairing

/-- The exact rank correction is nonnegative for every drawn prime-order group.

**Proof sketch.** Each factor of the invertible-matrix fraction lies between zero and one
because the prime order is at least two. Their product is at most one. -/
theorem rankSlack_nonneg {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) :
    0 ≤ rankSlack pp := sorry

/-- The exact three-by-three rank correction is at most 3/p.
This coarse upper bound preserves the exact loss in the core inequality.

**Proof sketch.** For factors in [0,1], one minus their product is at most the sum of
one minus each factor. Bound 1/p² and 1/p³ by 1/p, using p≥2. -/
theorem rankSlack_le_three_div {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) :
    rankSlack pp ≤ 3 / (pp.group.order : ℝ) := sorry

/-- Averaging the nonnegative exact rank correction preserves nonnegativity.

**Proof sketch.** Apply the shared expectation monotonicity and constant expectation readers
to the pointwise nonnegative correction. -/
theorem linearSlack_nonneg (G : BilinearGen) (κ : ℕ) : 0 ≤ linearSlack G κ := sorry

/-- Every fixed prime schedule bounds the averaged correction by 3/p(κ).

**Proof sketch.** Use order_eq_of_publicParams to replace every drawn order by p(κ),
then average rankSlack_le_three_div and apply the constant expectation reader. -/
theorem linearSlack_le_fixedOrder (G : BilinearGen) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) :
    linearSlack G κ ≤ 3 / (p κ : ℝ) := sorry

/-- Exponential order growth makes the exact rank correction subexponentially small at
any positive exponent below one [JLS26, Section 1.1].

**Proof sketch.** Bound the nonnegative correction by 3·2⁻κ using the fixed-order bound.
Use subexpSmall_two_pow_neg and the shared constant-multiple and domination closures at
the requested smaller exponent. No negligible estimate is reproved locally. -/
theorem linearSlack_subexpSmall (G : BilinearGen) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) : SubexpSmall c (linearSlack G) := sorry

/-- Exponential order growth makes the exact rank correction negligible.

**Proof sketch.** Apply linearSlack_subexpSmall at exponent one half and the shared
SubexpSmall.negligible theorem. -/
theorem linearSlack_negligible (G : BilinearGen) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ) :
    Negligible (linearSlack G) := sorry

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
