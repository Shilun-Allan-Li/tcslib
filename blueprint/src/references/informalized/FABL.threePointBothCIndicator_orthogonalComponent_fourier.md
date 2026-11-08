<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.threePointBothCIndicator_orthogonalComponent_fourier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Component by Support

**Claim.** For every coordinate set $S\subseteq\{0,1\}$, the orthogonal component of the product indicator at support $S$ is the sum of the corresponding product Fourier basis functions, weighted by the products of the one-coordinate indicator coefficients.

**Proof.** By the support formula for orthogonal components (\texttt{FiniteFourierBasis.orthogonalComponent\_eq\_fourierComponentAtSupport}), this component is the sum over multi-indices whose nonzero coordinates are exactly $S$, with each term weighted by the Fourier coefficient of the product indicator. The coefficient table for that indicator (\texttt{threePointBothCIndicator\_fourierCoeff\_table}) identifies the coefficient at an index $(a_0,a_1)$ as the product of the one-coordinate coefficients, $\widehat g(a_0)\widehat g(a_1)$. Substituting this expression term by term gives the stated sum.

**Key facts.** `FABL.FiniteFourierBasis.orthogonalComponent_eq_fourierComponentAtSupport`, `FABL.threePointBothCIndicator_fourierCoeff_table`.
