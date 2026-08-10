<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: noise_param_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The dual-exponent noise parameter identity

**Claim.** If `0 < u − 1` then `(u / (u − 1) − 1) * (p − 1) = (p − 1) / (u − 1)`.
A `private` algebraic identity: passing from `u` to its Hölder conjugate
`u' = u/(u−1)` turns the two-function noise parameter `(u' − 1)(p − 1)` into the
one-function parameter `(p − 1)/(u − 1)`.

**Proof.** One line: `field_simp; ring`. The hypothesis `hu_pos` is exactly the
`u − 1 ≠ 0` that `field_simp` needs to clear the denominator.

**Used in.** `bridging_hypercontractivity`, as `h_noise_eq`: under `congr 1` it
shows `Real.sqrt ((u/(u−1) − 1) * (p − 1)) = Real.sqrt ((p − 1)/(u − 1)) = ρ`, so
the two-function bound obtained from `weak_two_function_hypercontractivity` at
exponents `(u/(u−1), p)` is stated at the same `ρ` as the target one-function
bound.
