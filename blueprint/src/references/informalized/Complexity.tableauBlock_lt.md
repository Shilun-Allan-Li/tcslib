<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.tableauBlock_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Earlier Tableau Blocks Lie Below Later Bases

**Claim.** If $s<t$, every vertex index in the tableau block at time $s$ is strictly less than the tableau base at time $t$.

**Proof.** Take any index in the block at time $s$. By the definition of that block, it is the vertex at time $s$ with some index $j$ strictly below the snapshot width. The vertex bound (`Complexity.tableauVertex_lt`) places this vertex strictly below the base at time $s+1$. Since $s<t$, we have $s+1\le t$, so monotonicity of the tableau base (`Complexity.tableauBase_mono`) gives that the base at time $s+1$ is at most the base at time $t$. Combining the strict and weak inequalities proves the result.

**Key facts.** `Complexity.tableauVertex_lt`, `Complexity.tableauBase_mono`.
