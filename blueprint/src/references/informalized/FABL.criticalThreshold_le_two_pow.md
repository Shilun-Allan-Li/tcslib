<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.criticalThreshold_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Threshold Upper Bound

**Claim.** For every positive integer $w$, the tribes critical threshold is at most $2^w$.

**Proof.** The elementary logarithm bound gives $\log 2\le 1$. Also, the critical logarithm estimate says that $2^{-w}\le -\log(1-2^{-w})$, and the critical logarithm is positive. Comparing these positive denominators and using $\log 2\le1$ yields
\[
\frac{\log 2}{-\log(1-2^{-w})}\le \frac{1}{2^{-w}}=2^w.
\]

**Key facts.** `FABL.criticalInverse_le_criticalLog`, `FABL.criticalLog_pos`.
