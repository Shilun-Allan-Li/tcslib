<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.excess_le_boundedNeighborInfluentialVertexFraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Excess and Influential Vertices

**Claim.** If the bounded table’s averaged-neighbor tester value is at least $\alpha+\operatorname{error}(\varepsilon)+\tau$, then $\tau$ is at most the fraction of vertices whose averaged-neighbor function has a coordinate with influence greater than $\varepsilon$.

**Proof.** Fix a vertex. If its averaged-neighbor function has an influential coordinate, its acceptance probability is at most $1$, since tester acceptance probabilities lie in $[0,1]$. As $\alpha>0$ and $\operatorname{error}(\varepsilon)\ge0$, this is at most $\alpha+\operatorname{error}(\varepsilon)+1$. If it has no such coordinate, every coordinate’s influence is at most $\varepsilon$, so the test’s soundness condition bounds its acceptance probability by $\alpha+\operatorname{error}(\varepsilon)$. Thus, in either case, the vertex’s acceptance probability is at most $\alpha+\operatorname{error}(\varepsilon)$ plus the indicator that the vertex is influential. Averaging over vertices gives an upper bound on the long-code value by $\alpha+\operatorname{error}(\varepsilon)$ plus the influential-vertex fraction. Comparing with the assumed lower bound and subtracting the common terms yields the result.

**Key facts.** `FABL.SignTester.acceptanceProbability_mem_Icc`, `FABL.hasSmallInfluences_iff`.
