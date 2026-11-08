<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.sum_erase_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of distinct-index sums

**Claim.** For any function $a$ on pairs of indices, the sum of $a(j,i)$ over ordered distinct pairs equals the sum of $a(i,j)$ over those pairs.

**Proof.** For each fixed $i$, summing $a(j,i)$ over $j\ne i$ is the sum over all $j$ minus the diagonal term $a(i,i)$. The same description holds for the sum of $a(i,j)$ over $j\ne i$. Summing both expressions over $i$ cancels the identical diagonal sums. What remains on each side is the sum over all ordered pairs, with the order of summation interchanged; finite double sums commute, so these totals agree.
