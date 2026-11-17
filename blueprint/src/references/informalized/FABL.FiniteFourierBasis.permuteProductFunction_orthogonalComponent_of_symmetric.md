<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.permuteProductFunction_orthogonalComponent_of_symmetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation of Fourier Components

**Claim.** If $f$ is invariant under coordinate permutations, then permuting its Fourier component indexed by $S$ gives the Fourier component indexed by the image of $S$ under the permutation.

**Proof.** Fix a coordinate permutation and define a candidate decomposition by taking, at each set $T$, the component of $f$ indexed by the inverse image of $T$, then permuting its input. Its components sum to $f$: reindex the sum of the original components by the inverse permutation, evaluate at the permuted input, and use the assumed permutation invariance of $f$. Each candidate component depends only on $T$, because permuting a function that depends only on a set makes it depend only on the image of that set.

For strict containment $U\subset T$ and a function $g$ depending only on $U$, pull $g$ back by the inverse permutation. This pulled-back function depends only on the inverse image of $U$, which is strictly contained in the inverse image of $T$. The original component is therefore orthogonal to the pulled-back function. The product inner product is invariant under simultaneous permutation of both inputs, so this orthogonality is exactly the required orthogonality for the candidate decomposition. By uniqueness it is the canonical decomposition of $f$. Evaluating it at the image of $S$ and simplifying the inverse-image and image operations yields the stated identity.

**Key facts.** `FABL.FiniteFourierBasis.sum_orthogonalComponent`, `FABL.FiniteFourierBasis.orthogonalComponent_dependsOnly`, `FABL.permuteProductFunction_dependsOnly`, `FABL.FiniteFourierBasis.productInner_orthogonalComponent_eq_zero_of_ssubset`, `FABL.productInner_permuteProductFunction`, `FABL.FiniteFourierBasis.orthogonalDecomposition_unique`.
