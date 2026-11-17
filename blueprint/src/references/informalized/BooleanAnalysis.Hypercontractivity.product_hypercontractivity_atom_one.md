<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/General.lean :: BooleanAnalysis.Hypercontractivity.product_hypercontractivity_atom_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hypercontractivity for Unit Atoms

**Claim.** If every coordinate atom has weight at least $1$ and $q>2$, then the product noise operator satisfies both stated norm inequalities for every real-valued $f$ and every $\rho$.

**Proof.** For each coordinate, its weights are positive and sum to $1$. Since every weight is at least $1$, each must equal $1$; in particular, each coordinate has only one possible value. Therefore the product space has a single point, and its mass is $1$.

The noise-kernel formula then reduces the noise operator to the identity: the kernel has total contribution $1$ at the unique point. On a one-point probability space, every moment norm of a function is the absolute value of its value (the relevant exponents are nonzero because $q>2$). Thus both inequalities reduce to equality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.noise_kernel`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.mass_sum`.
