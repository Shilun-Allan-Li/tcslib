<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.criticalThreshold_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Critical Threshold

**Claim.** For every positive integer $w$, the tribes critical threshold is nonnegative.

**Proof.** The numerator $\log 2$ is positive, and the critical logarithm $-\log(1-2^{-w})$ is positive by the critical logarithm positivity result. Their quotient is therefore nonnegative.

**Key facts.** `FABL.criticalLog_pos`.
