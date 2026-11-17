<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamStart_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup Length Invariant

**Claim.** For every bit string $x$, if its startup state has consumed length $u$ and fresh cursor $f$, then $u\le |x|$ and $f\le |x|+u$.

**Proof.** Split according to whether the input passes the syntax check. If it does, startup sets the consumed length to zero and the fresh cursor to the number of variables in the decoded formula. Zero is at most the input length, and the decoded variable count is bounded by that length, hence by the input length plus the consumed length. If the syntax check fails, startup sets the consumed length to $|x|$ and the fresh cursor to zero, which satisfies both inequalities directly.

**Key facts.** `Std.Sat.CNF.numVars_decode_le`.
