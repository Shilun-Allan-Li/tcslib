<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.cX_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-offset symbol query

**Claim.** For any optional tape index $\tau$ and time $t$, the signed query at offset zero equals the symbol query with the negative-sign flag set to false.

**Proof.** At offset zero, the test for whether the offset is negative is false, and its natural absolute value is zero. Unfolding the signed query therefore gives exactly the symbol query with sign flag false at indices $t$ and $0$.
