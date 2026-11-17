<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BooleanCharacteristic.lean :: BooleanAnalysis.GaussianSpace.sum_pair_coordinate_products -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorization of a Boolean Coordinate Sum

**Claim.** For a finite index set and arbitrary complex-valued functions $H_i$ on pairs of Boolean values, the sum over pairs of Boolean vectors of the product of coordinate contributions factors as the product of the individual two-sign-pair sums.

**Proof.** For each fixed vector $x$, expand the sum over $y$ of the coordinate product by distributing the finite sum independently across coordinates. This converts it into a product over $i$ of sums over the Boolean value $y_i$, with $x_i$ fixed. Now sum over $x$ and distribute that sum across the resulting product in the same way. Each coordinate contributes its own sum over $x_i$ and $y_i$, namely $\sum_{b}\sum_c H_i(b,c)$. Multiplying these coordinate sums gives the required factorization.
