<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.tableauSources_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tableau Sources Precede the Base

**Claim.** Every index in the source list for time $t$ is strictly less than the tableau base at time $t$.

**Proof.** Take an index from the source list and split according to which component contains it. A constant source is below the base by the constant-index bound (`tableauConst_lt`). An index in the preceding configuration block is below the current base by the block bound (`tableauBlock_lt`), since that block's time is earlier. For each work tape, if there has been no previous visit, its sources are constants; if there has, the flag is a constant and the remaining indices lie in the block at the last-visit time. That time is strictly earlier than $t$ (`prevVisit_lt`), so the block bound applies. The input-position source is either a constant or an earlier input index; in the latter case its being at most $n-1$ places it below the base, and in the former case the constant bound applies. Finally, the previous acceptance source is a constant when $t=0$; otherwise it is the acceptance vertex from time $t-1$. That vertex is below the base for time $t$, by the vertex-within-next-block bound (`tableauVertex_lt`) and monotonicity of the bases (`tableauBase_mono`).

**Key facts.** `Complexity.tableauConst_lt`, `Complexity.tableauBlock_lt`, `Complexity.prevVisit_lt`, `Complexity.tableauVertex_lt`, `Complexity.tableauBase_mono`.
