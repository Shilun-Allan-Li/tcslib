<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/CorrelationImmunityBounds.lean :: FABL.fourierCoeff_sq_eq_two_mul_empty_mul_of_large_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square Coefficient Under Large Support

**Claim.** If $S$ is nonempty and has nonzero Fourier coefficient, and every nonempty frequency with nonzero coefficient has size greater than $2n/3$, then the Fourier coefficient of $f^2$ at $S$ is twice the product of the constant coefficient and the coefficient at $S$.

**Proof.** The Fourier coefficient of a pointwise product is the convolution of the two coefficient functions over symmetric difference (`fourierCoeff_pointwise_mul`). For the square, the summand indexed by $T$ is therefore $\widehat f(T\mathbin{\triangle}S)\widehat f(T)$. If $T$ is neither empty nor $S$, then both $T$ and $T\mathbin{\triangle}S$ are nonempty. If this summand were nonzero, the hypothesis would force all three sets $S$, $T$, and $T\mathbin{\triangle}S$ to have size greater than $2n/3$. But $S=T\mathbin{\triangle}(T\mathbin{\triangle}S)$, and the three-large-sets obstruction rules this out (`not_three_large_of_eq_symmDiff`). Thus only $T=\varnothing$ and $T=S$ contribute. Their terms are each $\widehat f(\varnothing)\widehat f(S)$, since $\varnothing\mathbin{\triangle}S=S$ and $S\mathbin{\triangle}S=\varnothing$. Adding these two contributions proves the formula.

**Key facts.** `FABL.fourierCoeff_pointwise_mul`, `FABL.not_three_large_of_eq_symmDiff`.
