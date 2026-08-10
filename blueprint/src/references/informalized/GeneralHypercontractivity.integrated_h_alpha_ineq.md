<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: integrated_h_alpha_ineq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Integrated form of the two-point derivative inequality

**Claim.** Let `1 ≤ p ≤ q ≤ 2` and `0 ≤ b ≤ 1`, and put
`ρ = Real.sqrt ((p - 1) / (q - 1))` (bound by a `let` in the statement). Then

`((1 + ρ*b) ^ q + (1 - ρ*b) ^ q - 2) / q ≤ ((1 + b) ^ p + (1 - b) ^ p - 2) / p`.

This is `h_alpha_ineq` integrated from `0` to `b`.

**Proof.**

1. Set
   `g t = ((1+t)^p + (1-t)^p - 2)/p - ((1+ρ*t)^q + (1-ρ*t)^q - 2)/q`;
   the goal is `0 ≤ g b`.
2. On `Set.Ioo 0 b`, a `HasDerivAt.rpow_const` / `HasDerivAt.div_const` chain
   gives
   `deriv g t = ((1+t)^(p-1) - (1-t)^(p-1)) - ρ * ((1+ρ*t)^(q-1) - (1-ρ*t)^(q-1))`
   (the `p, q ≠ 0` side conditions come from `1 ≤ p ≤ q`).
3. That expression is `≥ 0` by `h_alpha_ineq` with `r = p-1`, `s = q-1`,
   `c = ρ` — the hypothesis `c = √(r/s)` holds by `rfl`, and `0 ≤ r ≤ s ≤ 1`
   is exactly `1 ≤ p ≤ q ≤ 2`.
4. If `b = 0` both sides are `0` (`norm_num [hb]`). Otherwise
   `exists_deriv_eq_slope g` on `[0, b]`, used contrapositively, needs only
   continuity and differentiability of `g` there (assembled from
   `ContinuousAt.rpow` / `DifferentiableAt.rpow_const`, bases positive since
   `0 ≤ ρ*t ≤ t < b ≤ 1`); combined with step 3 and `g 0 = 0` it yields
   `0 ≤ g b`.

**Used in.** `two_point_ineq_general_unit`, where together with
`rpow_ge_one_add_mul_sub` it produces the general two-point inequality
`((1+ρb)^q + (1-ρb)^q)/2 ≤ (((1+b)^p + (1-b)^p)/2)^(q/p)` driving one-bit
`(p,q)`-hypercontractivity for `1 < p ≤ q ≤ 2`.
