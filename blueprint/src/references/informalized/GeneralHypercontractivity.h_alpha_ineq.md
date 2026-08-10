<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: h_alpha_ineq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Derivative form of the two-point inequality

**Claim.** Let `0 ≤ r ≤ s ≤ 1`, let `c = Real.sqrt (r / s)`, and let `0 ≤ t ≤ 1`.
Then `(1 + t) ^ r - (1 - t) ^ r ≥ c * ((1 + c*t) ^ s - (1 - c*t) ^ s)`
(all powers `rpow`).

**Proof.**

1. If `r = 0` both sides are `0` (`c = √0 = 0`): closed by `aesop`.
2. Otherwise `0 < r ≤ s`, and `0 ≤ c ≤ 1` because `r/s ≤ 1`
   (`Real.sqrt_le_iff`, `div_le_iff₀`). Set
   `g t = (1+t)^r - (1-t)^r - c*((1+c*t)^s - (1-c*t)^s)`; the goal is `0 ≤ g t`.
3. `deriv g` on `Set.Ioo 0 1`, computed by a `HasDerivAt.rpow_const` chain:
   `deriv g t = r * ((1+t)^(r-1) + (1-t)^(r-1) - (c^2*s/r) * ((1+c*t)^(s-1) + (1-c*t)^(s-1)))`.
   Since `c^2 = r/s` (`Real.sq_sqrt`), the coefficient `c^2*s/r` is `1`.
4. The bracket is nonnegative for `t ∈ (0,1)`, in two steps:
   - `rpow_sum_antitone_exponent` (exponents `r-1 ≤ s-1 ≤ 0`) gives
     `(1+t)^(r-1) + (1-t)^(r-1) ≥ (1+t)^(s-1) + (1-t)^(s-1)`;
   - `x ↦ (1+x)^(s-1) + (1-x)^(s-1)` has nonnegative derivative
     `(s-1)*((1+x)^(s-2) - (1-x)^(s-2))` on `(0,t)`, so by
     `exists_deriv_eq_slope` it is monotone and shrinking `t` to `c*t ≤ t` only
     decreases it (the degenerate case `c = 1` is handled separately).
   Hence `0 ≤ deriv g` on `(0,1)` by `mul_nonneg hr`.
5. `by_contra` plus `exists_deriv_eq_slope` on `[0, t]` (continuity and
   differentiability of the four `rpow` terms discharged from `0 < 1 ± x`,
   `0 < 1 ± c*x`) gives a point `ξ` with `deriv g ξ = (g t - g 0)/t`; with
   `g 0 = 0` and `deriv g ξ ≥ 0` this contradicts `g t < 0`.

**Used in.** `integrated_h_alpha_ineq`, instantiated at `r = p-1`, `s = q-1`,
`c = ρ`, where it is exactly the derivative of the integrated inequality.
