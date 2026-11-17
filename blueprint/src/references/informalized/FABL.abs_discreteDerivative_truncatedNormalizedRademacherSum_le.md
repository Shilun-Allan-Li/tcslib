<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.abs_discreteDerivative_truncatedNormalizedRademacherSum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truncated Sum Derivative Bound

**Claim.** For positive $n$, the absolute value of the discrete derivative in any coordinate of the truncated normalized Rademacher sum is at most $1/\sqrt n$.

**Proof.** Write the derivative as half the difference between the function values obtained by setting coordinate $i$ to $1$ and to $-1$ (`discreteDerivative_apply`). Truncation by projection onto $[-1,1]$ cannot increase the absolute difference between two real numbers, by the nonexpansiveness of interval projection. Before truncation, changing that coordinate changes the normalized sum by exactly $2(\sqrt n)^{-1}$ (`normalizedRademacherSum_setCoordinate_sub`). Therefore the truncated values differ by at most this amount; dividing their difference by $2$ in the derivative formula gives the claimed bound.

**Key facts.** `FABL.normalizedRademacherSum_setCoordinate_sub`, `FABL.discreteDerivative_apply`.
