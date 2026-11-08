<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.ConfigCount.posCode_injOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the bounded position code

**Claim.** For integers $z,z'$ with $|z|,|z'|\le B$, equality of their position codes implies $z=z'$.

**Proof.** The bounds place both integers in the interval $[-B,B]$. On this interval, adding $B$ gives a nonnegative integer at most $2B$, so the code's truncated natural-number value is exactly $z+B$ (and similarly $z'+B$). Equality of the codes therefore gives $z+B=z'+B$, and cancellation yields $z=z'$.
