<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.edgeMajority_isMonotoneGraphProperty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Edge Majority

**Claim.** The edge-majority graph property is monotone: if every edge present in $G$ is also present in $H$, then edge majority for $G$ implies edge majority for $H$.

**Proof.** Assume every edge present in $G$ is present in $H$. For each possible edge, its contribution to the edge count is either $0$ or $1$; the assumption ensures that a contribution of $1$ for $G$ is also $1$ for $H$. Thus the edge count of $G$ is at most that of $H$. The edge-majority condition for $G$ says that the total number of possible edges is at most twice its edge count. Combining this inequality with the count comparison gives the same condition for $H$.
