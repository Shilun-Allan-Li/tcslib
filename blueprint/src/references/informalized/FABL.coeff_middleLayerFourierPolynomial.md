<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.coeff_middleLayerFourierPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Middle-Layer Fourier Polynomial Coefficient

**Claim.** For a $k$-element set $T$ of the $2m$ coordinates, the coefficient of $t^k$ in the middle-layer Fourier polynomial is $\binom{2m}{k}$ times the Fourier coefficient at $T$.

**Proof.** Taking the coefficient of $t^k$ in the defining sum retains exactly those terms indexed by sets $U$ with $|U|=k$. The middle-layer indicator is symmetric under coordinate permutations, so Fourier coefficients of sets with the same cardinality agree (\texttt{fourierCoeff\_eq\_of\_card\_eq\_of\_isSymmetric}); symmetry of the indicator supplies the hypothesis (\texttt{middleLayerIndicator\_isSymmetric}). Hence every retained term equals the coefficient at $T$. There are $\binom{2m}{k}$ such sets, so their sum is the claimed product.

**Key facts.** `FABL.middleLayerIndicator_isSymmetric`, `FABL.fourierCoeff_eq_of_card_eq_of_isSymmetric`.
