<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean :: johnson_lindenstrauss -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a Johnson–Lindenstrauss Embedding

**Claim.** Under the stated dimension bound, there exists a linear map into the $k$-dimensional Euclidean space that preserves all pairwise squared distances in $V$ within factors $1-\varepsilon$ and $1+\varepsilon$.

**Proof.** First, the dimension estimate gives $k>0$ and makes the union-bound failure estimate strictly less than one (`jl_failure_bound_of_dim`). Next choose a probability space carrying a measurable random matrix whose entries are independent Gaussians with variance $1/k$ (`exists_iid_gaussian_matrix`). For each pair $u,v\in V$, the bad event for the difference vector $u-v$ is measurable (`measurableSet_badSingle`). The Gaussian Johnson–Lindenstrauss theorem (`johnson_lindenstrauss_of_gaussian`) bounds each such event by the single-vector tail estimate; summing over the at most $|V|^2$ ordered pairs bounds the probability of any failure by the quantity already shown to be less than one. Hence there is an outcome for which no pair fails. Fix that matrix and take its associated linear map; its simultaneous pairwise distortion bounds give the required embedding.

**Key facts.** `jl_failure_bound_of_dim`, `exists_iid_gaussian_matrix`, `measurableSet_badSingle`, `johnson_lindenstrauss_of_gaussian`.
