<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean :: johnson_lindenstrauss_of_gaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Johnson–Lindenstrauss embedding

**Claim.** Under the stated Gaussian entry laws and independence assumptions, if the sum of the pairwise failure bounds is less than one, there is a linear map that preserves all squared distances in the finite set within relative error ε.

**Proof.** For each pair $u,v\in V$, apply the Gaussian single-vector concentration bound to $u-v$. It says that the probability that the squared norm of its image deviates from $\|u-v\|^2$ by more than the allowed relative error is at most $2\exp(-k\varepsilon^2/8)$. Thus every pair has the required failure-probability bound. The measurable bad events can be union-bounded over the at most $|V|^2$ ordered pairs. The hypothesis says this total probability is less than one, so there is an outcome for which no pair is bad. The matrix at that outcome, viewed as a linear map, gives the asserted embedding.

**Key facts.** `jl_concentration_single`, `exists_isJLEmbedding_of_pair_bound`.
