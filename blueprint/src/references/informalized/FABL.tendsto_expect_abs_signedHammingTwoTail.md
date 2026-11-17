<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.tendsto_expect_abs_signedHammingTwoTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Hamming tail expectation limit

**Claim.** For every $t\ge0$, the uniform-cube expectation of the absolute difference between the two upper-tail indicators, evaluated at $x$ and $-x$ in dimension $m+1$, tends to twice the standard Gaussian upper-tail probability at $t$.

**Proof.** For each dimension, the expectation of the absolute signed difference equals twice the expectation of the upper-tail indicator (`expect_abs_signedHammingTwoTail`). The latter expectation in dimension $m+1$ tends to the standard Gaussian upper-tail probability at $t$ (`tendsto_expect_hammingUpperTailIndicator`). Multiplying this convergent sequence by $2$ gives the stated limit.

**Key facts.** `FABL.expect_abs_signedHammingTwoTail`, `FABL.tendsto_expect_hammingUpperTailIndicator`.
