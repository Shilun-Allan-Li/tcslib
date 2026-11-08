<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.excess_le_boundedNeighborNotableVertexFraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Excess and Notable Vertices

**Claim.** If the bounded table’s averaged-neighbor tester value is at least $\alpha+\operatorname{error}(\varepsilon)+\tau$, then $\tau$ is at most the fraction of vertices whose averaged-neighbor function has a coordinate with stable influence greater than $\varepsilon$.

**Proof.** Fix a vertex. If its averaged-neighbor function has a notable coordinate, its tester acceptance probability is at most $1$. Since $\alpha>0$ and $\operatorname{error}(\varepsilon)\ge0$, this is bounded by $\alpha+\operatorname{error}(\varepsilon)+1$. If it has no notable coordinate, every coordinate has stable influence at most $\varepsilon$, so the test’s soundness condition bounds acceptance by $\alpha+\operatorname{error}(\varepsilon)$. Therefore, pointwise, acceptance is bounded by $\alpha+\operatorname{error}(\varepsilon)$ plus the indicator of being notable. Averaging over vertices bounds the long-code value by $\alpha+\operatorname{error}(\varepsilon)$ plus the notable-vertex fraction. Comparing this with the assumed lower bound and subtracting the common terms gives the claim.

**Key facts.** `FABL.SignTester.acceptanceProbability_mem_Icc`.
