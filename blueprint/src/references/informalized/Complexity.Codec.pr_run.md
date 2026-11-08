<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.pr_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Scan of a Paired Word

**Claim.** The scan rejects after advancing the position by some number of steps no larger than the remaining suffix length when decoding that suffix fails. When decoding succeeds with first component $u$, it reaches the prescribed continuation after advancing by $2|u|+2$, with the other registers unchanged.

**Proof.** Apply the aligned-pair scanning principle (`alignedPair_loop`) to the suffix of $y$ beginning at the position register. Its hypotheses match the program's scan, first-read, test, read, and advance instructions: the scan stops at the length register; the initial read and subsequent reads query the bit oracle at the current position; and each advance increments that position by one. Each paired payload bit is represented twice, so a successful decoded first component $u$ consumes $2|u|$ bits, followed by the two-bit separator. The loop therefore reaches the continuation after $2|u|+2$ increments. If decoding fails, the loop reaches rejection after a number of increments bounded by the suffix length.

The length and position hypotheses ensure the scan's position remains within the input extent, while the register bound hypothesis supplies the required bound for the reachability guard. The oracle answers used by the scan are the corresponding input bits: `orc_bit` identifies a bit query on an encoded word with the indexed bit, and `getD_drop` relates that bit in the suffix to the bit at the offset position in $y$. The final arithmetic identifies the scan's offset index with the current position.

**Key facts.** `Complexity.LogProg.alignedPair_loop`, `Complexity.Codec.orc_bit`, `Complexity.getD_drop`.
