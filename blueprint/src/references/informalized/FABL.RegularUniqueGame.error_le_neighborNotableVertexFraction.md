<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.error_le_neighborNotableVertexFraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Error and Notable Vertex Fraction

**Claim.** If the tester's long-code value is at least $\alpha+2\operatorname{error}(\varepsilon)$, then $\operatorname{error}(\varepsilon)$ is at most the fraction of vertices whose averaged neighbor function has a coordinate with stable influence greater than $\varepsilon$.

**Proof.** Fix a vertex. If it has a notable coordinate, its tester acceptance probability is at most $1$, since acceptance probabilities lie in $[0,1]$ (`SignTester.acceptanceProbability_mem_Icc`). This is at most $\alpha+\operatorname{error}(\varepsilon)+1$, using the nonnegativity of $\alpha$ and of the error. If it has no notable coordinate, every coordinate's stable influence is at most $\varepsilon$; the test's soundness assumption bounds acceptance by $\alpha+\operatorname{error}(\varepsilon)$. Thus at each vertex acceptance is at most $\alpha+\operatorname{error}(\varepsilon)$ plus the indicator of having a notable coordinate. Averaging over vertices gives the same upper bound for the long-code value, with the indicator average equal to the notable-vertex fraction. Comparing with the assumed lower bound and subtracting $\alpha+\operatorname{error}(\varepsilon)$ proves the claim.

**Key facts.** `FABL.SignTester.acceptanceProbability_mem_Icc`.
