<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/ExpPoly.lean :: Complexity.pow_mono_deg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of natural powers

**Claim.** For natural numbers $n,k,k'$, if $k\le k'$, then $(n+1)^k\le(n+1)^{k'}$.

**Proof.** Since $n+1\ge 1$, powers of $n+1$ are nondecreasing in the exponent. Applying this monotonicity to $k\le k'$ gives the claimed inequality.
