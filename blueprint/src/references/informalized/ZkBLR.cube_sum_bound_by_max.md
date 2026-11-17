<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.cube_sum_bound_by_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier cube-sum bound

**Claim.** If every Fourier coefficient of the lifted function has magnitude at most $A$, then the sum of their cubed magnitudes is at most $A$ times the sum of their squared magnitudes.

**Proof.** For each frequency $s$, let $r=|\widehat{\widetilde f}(s)|$. The norm is nonnegative, so $r^2\ge0$, and the hypothesis gives $r\le A$. Therefore $r^3=r\,r^2\le A r^2$. Summing this pointwise inequality over all frequencies and factoring the constant $A$ out of the finite sum proves the result.
