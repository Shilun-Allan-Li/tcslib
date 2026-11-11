<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: jl_concentration_single_rademacher -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rademacher Projection Concentration

**Claim.** For a fixed nonzero vector, the probability that the squared norm of its image under the normalized Rademacher matrix differs from its squared norm by more than an ε-fraction is at most $2\exp(-k\varepsilon^2/8)$.

**Proof.** Apply the general single-vector sub-Gaussian concentration theorem to the row projections of the normalized Rademacher matrix. The projections are measurable (`radMatrix_proj_meas`) and independent (`radMatrix_proj_indep`). For each row, its moment-generating function is bounded by that of a centered sub-Gaussian with variance proxy $\|x\|^2/k$ (`hasSubgaussianMGF_row_proj`), and its second moment equals $\|x\|^2/k$ (`integral_sq_row_proj`). These are precisely the projection bounds required by the general theorem, which gives the stated deviation probability.

**Key facts.** `radMatrix_proj_meas`, `radMatrix_proj_indep`, `hasSubgaussianMGF_row_proj`, `integral_sq_row_proj`, `jl_concentration_single_subgaussian`.

**Caveat.** The supplied informal statement describes a single Rademacher sum, but the formal theorem concerns squared-norm concentration for a normalized Rademacher matrix; the account follows the formal statement and proof.
