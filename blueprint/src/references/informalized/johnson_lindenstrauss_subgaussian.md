<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean :: johnson_lindenstrauss_subgaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sub-Gaussian Johnson–Lindenstrauss dimension bound

**Claim.** For the stated dimension bound on $k$, every finite set of at most $n$ points admits a linear embedding into the $k$-dimensional space that preserves squared distances within relative error ε.

**Proof.** First, the dimension estimate implies that $k$ is positive and that $|V|^2\,2\exp(-k\varepsilon^2/8)<1$; this is the numerical failure-bound lemma. Use the joint Rademacher measure and its random sign matrix. The matrix is measurable, and its row projections are measurable and independent. For each fixed vector, the row projection has sub-Gaussian moment-generating-function bound with parameter $\|x\|^2/k$ and second moment $\|x\|^2/k$, giving the hypotheses required by the structural sub-Gaussian embedding theorem. The bad events are measurable. Applying that theorem with these data and the failure estimate produces the desired embedding.

**Key facts.** `jl_failure_bound_of_dim`, `measurableSet_badSingle`, `measurable_radMatrix`, `radMatrix_proj_meas`, `radMatrix_proj_indep`, `hasSubgaussianMGF_row_proj`, `integral_sq_row_proj`, `johnson_lindenstrauss_of_subgaussian`.
