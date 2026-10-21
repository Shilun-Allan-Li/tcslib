<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: delta_tau_involution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The map δ ↦ 1/2 − √(δ(1−δ)) is an involution on [0, 1/2]

**Claim.** For real `δ` with `0 ≤ δ` and `δ ≤ 1/2`, setting
`τ := 1 / 2 - Real.sqrt (δ * (1 - δ))` one has
`δ = 1 / 2 - Real.sqrt (τ * (1 - τ))`. (The `τ` is a `let` in the statement, so
the goal is literally the displayed equation with `τ` substituted.)

**Proof.** Write `s = Real.sqrt (δ * (1 - δ))`, so `τ = 1/2 - s` and
`τ * (1 - τ) = (1/2 - s) * (1/2 + s) = 1/4 - s²`.

1. `ring_nf` normalizes the goal into that form, exposing `s ^ 2`.
2. `rw [Real.sq_sqrt (by nlinarith)]` replaces `s ^ 2` by `δ * (1 - δ)`; the
   side goal `0 ≤ δ * (1 - δ)` follows from `0 ≤ δ ≤ 1/2` by `nlinarith`. The
   radicand is now `1/4 - δ(1 - δ) = (δ - 1/2)²`.
3. `rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq']` moves the remaining square
   root alone onto one side, leaving `√(1/4 - δ(1-δ)) = 1/2 - δ`.
4. `rw [Real.sqrt_eq_iff_mul_self_eq]` turns that into the polynomial identity
   `(1/2 - δ) * (1/2 - δ) = 1/4 - δ(1 - δ)` together with the positivity side
   goals; all are discharged by `nlinarith` from the bounds on `δ`, using
   `δ ≤ 1/2` for the sign `0 ≤ 1/2 - δ`.

**Used in.** The assembly of `mrrw_bound`: the bound is proved for a parameter
`τ` with `t_n / n → τ` (via `smallest_zero_asymptotic` and
`entropy_growth_of_objective`, whose limits are stated as
`1/2 - √(τ(1-τ))`), and this involution is what lets that be read back as the
target `rate δ ≤ binaryEntropy (1/2 - √(δ(1-δ)))`.
