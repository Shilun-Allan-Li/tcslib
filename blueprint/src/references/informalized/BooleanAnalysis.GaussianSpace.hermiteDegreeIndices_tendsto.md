<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Truncation.lean :: BooleanAnalysis.GaussianSpace.hermiteDegreeIndices_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exhaustion by Hermite Degree Indices

**Claim.** Every finite collection of multi-indices is contained in the degree-index sets for all sufficiently large degree bounds.

**Proof.** The membership characterization says that a multi-index $\alpha$ lies in the set of degree at most $k$ exactly when its total degree $\sum_i\alpha_i$ is at most $k$ (`mem_hermiteDegreeIndices`). This characterization shows the sets are increasing with $k$. For any given multi-index $\alpha$, it belongs to the set with bound $k=\sum_i\alpha_i$. Thus the increasing family eventually contains each index, which is precisely its tendency to the top among finite sets.

**Key facts.** `BooleanAnalysis.GaussianSpace.mem_hermiteDegreeIndices`.
