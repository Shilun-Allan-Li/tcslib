<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.summable_binVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summability of binary values

**Claim.** For every Boolean sequence $p$, the series with term $2^{-(i+1)}$ when $p(i)$ is true and zero otherwise is summable.

**Proof.** The terms are nonnegative. Each is bounded above by $2^{-(i+1)}$, the corresponding term of a convergent geometric series. The comparison test for nonnegative series therefore gives summability.
