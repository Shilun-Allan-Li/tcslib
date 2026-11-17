<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Trace_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trace Assignment on Input Positions

**Claim.** For every finite-state binary machine $M$, state code, input word $y$, and index $j<|y|$, the trace assignment at position $j$ equals the bit of $y$ there, with false as the default when needed.

**Proof.** Because $j<|y|$, the trace assignment uses its initial-input branch, which returns the $j$th bit of $y$ with the stated default. This is exactly the claimed equality.
