<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.FiniteDecisionTree.queries_permuteCoordinates_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate permutation of query traces

**Claim.** The permuted tree queries coordinate $i$ on input $x$ exactly when the original tree queries $\sigma^{-1}(i)$ on the input whose value at $j$ is $x(\sigma(j))$.

**Proof.** The query trace of the permuted tree is the image under $\sigma$ of the original trace evaluated at the reindexed input (\texttt{queryTrace_permuteCoordinates}). Therefore, membership of $i$ in the permuted trace means that some coordinate $j$ in the original trace maps to $i$ under $\sigma$. Since $\sigma$ is injective, this forces $j=\sigma^{-1}(i)$, yielding membership of that coordinate in the original trace. Conversely, if $\sigma^{-1}(i)$ occurs in the original trace, its image under $\sigma$ is $i$, so $i$ occurs in the permuted trace.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_permuteCoordinates`.
