<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Truncation.lean :: BooleanAnalysis.GaussianSpace.mem_hermiteDegreeIndices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Hermite Degree Indices

**Claim.** A multi-index $\alpha\colon\{1,\ldots,n\}\to\mathbb N$ belongs to the Hermite degree indices of order $k$ exactly when $\sum_i\alpha_i\le k$.

**Proof.** Membership in the defined set means that $\alpha$ passes the filter requiring $\sum_i\alpha_i\le k$ and is the image of some tuple with each coordinate in $\{0,\ldots,k\}$. Hence membership immediately implies the sum bound. Conversely, assume the sum bound. For each coordinate $i$, nonnegativity of all summands gives $\alpha_i\le\sum_j\alpha_j\le k$, so $\alpha_i<k+1$. Thus the tuple whose coordinates are the $\alpha_i$ lies in the required finite product, and its image is exactly $\alpha$. Together with the assumed sum bound, this proves membership.
