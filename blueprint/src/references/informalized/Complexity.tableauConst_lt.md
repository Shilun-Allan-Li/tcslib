<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.tableauConst_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tableau Constants Lie Below the Base

**Claim.** For every finite-state Boolean-input machine $M$, all natural numbers $n,t$, and each Boolean value $b$, the index assigned to the constant $b$ is strictly less than the tableau base $n+2+tW$.

**Proof.** If $b$ is true, its index is $n+1$; otherwise its index is $n$. In either case the index is at most $n+1$. The tableau base is $n+2+tW$, which is at least $n+2$ because $tW$ is nonnegative. Hence the constant index is strictly below the base.
