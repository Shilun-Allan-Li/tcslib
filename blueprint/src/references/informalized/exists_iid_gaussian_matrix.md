<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean :: exists_iid_gaussian_matrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independent Gaussian matrix

**Claim.** For positive $k$ and any $d$, there is a probability space carrying a measurable $k\times d$ random matrix whose entries each have law $\mathcal N(0,1/k)$, whose entries are jointly independent within every row, and whose rows are jointly independent.

**Proof.** Let $\sigma=1/k$, and take the sample space to be the set of arrays $\omega=(\omega_{ij})_{i\in\mathrm{Fin}(k),\,j\in\mathrm{Fin}(d)}$. Give each row the product measure with every coordinate distributed as $\mathcal N(0,\sigma)$, then give the arrays the outer product measure of these row measures. Define $A(\omega)_{ij}=\omega_{ij}$. Coordinate projections are measurable, so the resulting matrix-valued map is measurable. Under a product measure, each coordinate projection has its corresponding factor measure; applying this first to the row coordinate and then to the coordinate within that row shows that each entry has law $\mathcal N(0,\sigma)$. For a fixed row, its joint law is the inner product measure by the same product-measure projection property. Its coordinate marginals are all $\mathcal N(0,\sigma)$, so that joint law is the product of its marginals, which is precisely joint independence of the entries in that row. Finally, the outer product measure makes the row projections jointly independent, since each row projection is the identity-valued coordinate map on its factor.
