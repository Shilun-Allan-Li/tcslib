<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic-Space Access Language

**Claim.** For either mode, the language of pair encodings whose access value is true is decidable by a deterministic Turing machine using space bounded by a constant multiple of logarithmic input length.

**Proof.** The access procedure has a safe accepting or rejecting terminal configuration on each input (`Complexity.LogProg.access_run`). A safe access path can be converted into an ordinary finite-machine run, preserving its result and bounding the simulated work-tape positions (`Complexity.LogProg.accessPath_run`, `Complexity.LogProg.compile_space`). In this application the four work-tape heads stay between $-1$ and $W$, where $W$ is the bit-length of $|y|+1$; at the terminal configuration the same bounds hold. The resulting simulation therefore uses at most $4(W+2)$ cells. Binary bit-length is at most logarithmic (`Complexity.LogProg.length_bits_le_log`), and the input length $|y|$ is bounded by a linear polynomial in the actual encoded input length. The logarithm of such a polynomial is bounded by a constant multiple of the logarithm of that input length (`Complexity.LogProg.log_poly_bound`). Combining these bounds gives a constant $4C+8$ times the stated logarithmic space bound, so the language belongs to LOGSPACE.

**Key facts.** `Complexity.LogProg.log_poly_bound`, `Complexity.LogProg.access_run`, `Complexity.LogProg.accessPath_run`, `Complexity.LogProg.compile_space`, `Complexity.LogProg.length_bits_le_log`.
