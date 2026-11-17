<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.tableauBase_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Tableau Base

**Claim.** For times $s\le t$, the tableau base at time $s$ is at most the tableau base at time $t$.

**Proof.** The tableau base has the form $n+2+sW$, where $W$ is the fixed tableau width. Since $s\le t$ and $W$ is nonnegative, multiplication preserves the inequality, giving $sW\le tW$. Adding the same offset $n+2$ yields the claimed comparison.
