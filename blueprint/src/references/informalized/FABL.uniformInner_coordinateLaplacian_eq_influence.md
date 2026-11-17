<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DiscreteDerivatives.lean :: FABL.uniformInner_coordinateLaplacian_eq_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate influence and the Laplacian

**Claim.** For a real-valued function on the Boolean cube, its uniform inner product with its coordinate Laplacian equals its influence in that coordinate.

**Proof.** By Plancherel, the inner product is the sum over all subsets $S$ of the product of the Fourier coefficients of $f$ and $L_i f$. The Fourier coefficient of $L_i f$ is the coefficient of $f$ when $i\in S$, and is zero otherwise (\texttt{FABL.fourierCoeff_coordinateLaplacian}). Thus the sum reduces to $\sum_{S:\,i\in S}\widehat f(S)^2$. This is precisely the Fourier formula for the influence (\texttt{FABL.influence_eq_sum_sq_fourierCoeff}), proving the identity.

**Key facts.** `FABL.plancherel`, `FABL.fourierCoeff_coordinateLaplacian`, `FABL.influence_eq_sum_sq_fourierCoeff`.
