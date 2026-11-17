<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSoundInput.lean :: Complexity.Meyer.correct_all -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness at Every Bounded Time

**Claim.** If every local check passes and $x_b$ agrees with the input on its indices, then for every $t<2^W$ the table correctly gives all state and output answers, all work-tape symbols in the stated time-dependent range, and all input symbols in the stated offset range.

**Proof.** Proceed by induction on $t$. At time zero, the initial-time correctness theorem (`correct_zero`) gives all three parts of the required correctness statement, using the local checks and the agreement of $x_b$ with the input. For the successor case, suppose correctness holds at time $t$ and $t+1<2^W$. The one-step preservation theorem (`correct_succ`) then gives correctness at time $t+1$. The bound needed for the induction hypothesis follows from $t+1<2^W$.

**Key facts.** `Complexity.Meyer.correct_zero`, `Complexity.Meyer.correct_succ`.
