<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.FinNDTM.count_windowed_vertices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on windowed configurations

**Claim.** If the first $t+1$ configurations are windowed within radius $s$ and their cores together with output summaries are distinct, then $t+1$ is at most $3(|Q|+1)(|x|+2)3^{k(2s+1)}(2s+1)^k$.

**Proof.** Encode each configuration by its core restricted to the window of radius $s$, together with the summary of its output. The window bounds ensure that every work-head position lies among the $2s+1$ positions in that window, and that no nonblank tape cell lies outside it. Equality of the restricted core codes therefore implies equality of the full cores (`coreCode_inj`, using the window bounds supplied by `Cfg.InWindow.core_bounds`). Equality of output-summary codes implies equality of the summaries (`outSummaryCode_injective`). Thus distinct cores together with summaries give an injective encoding of the indices $0,[31m\ldots[0m,t$. The number of possible codes bounds the number of these indices: there are $|Q|+1$ choices for the state, $|x|+2$ input-head positions, three possible cell contents at each of the $k(2s+1)$ work-tape positions, $(2s+1)^k$ choices of work-head positions, and three output summaries. Multiplying these counts gives the claimed bound.

**Key facts.** `Turing.Cfg.InWindow.core_bounds`, `Turing.MultiTapeTM.ConfigCount.coreCode_inj`, `Turing.outSummaryCode_injective`.
