<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: count_bad_S_or -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Bad-seed bound for the OR approximator, unconditionally

**Claim.** For *every* `v : Fin width → ZMod p` (no nonvanishing hypothesis),

`#{S : Fin ℓ → Finset (Fin width) | approxOr_val p v S ≠ OR_val p v} * 2 ^ ℓ ≤ Fintype.card (Fin ℓ → Finset (Fin width))`.

**Proof.** `by_cases hv : v = 0`.

- If `v = 0`, then `approxOr_failure_iff` says failure requires `v ≠ 0`, so the filtered
  set is empty and the left side is `0`; `simp [approxOr_failure_iff, hv]` closes it.
- Otherwise `exact count_bad_S v hv`.

**Remark.** A two-line wrapper whose only job is to drop the `v ≠ 0` side condition, so
that callers can instantiate `v` with an arbitrary evaluation vector
`fun i ↦ (polys i).eval y` without first proving it nonzero.

**Used in.** `approxOr_pointwise_bad_count`, which combines it with `approxOr_eval_eq` and
`approxSeed_card` to state the bound in terms of `2 ^ (width * ℓ)`.
