<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaFourierGap.lean :: FABL.inv_two_pow_card_le_abs_fourierCoeff_of_dependsOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound for a nonzero Fourier coefficient

**Claim.** If a Boolean function depends only on the coordinates in $J$ and its Fourier coefficient at $S$ is nonzero, then that coefficient has absolute value at least $2^{-|J|}$.

**Proof.** The proof first transfers the dependence of the sign-valued function to its real-valued version (`dependsOn_toReal_iff`). If $S$ were not contained in $J$, the Fourier coefficient would vanish by the vanishing theorem for frequencies outside the coordinates on which a function depends (`fourierCoeff_eq_zero_of_dependsOn_of_not_subset`). Hence $S\subseteq J$. Represent this frequency inside the free coordinates of $J$ by $A$, the free part of $S$; its lift is exactly $S$ (`liftFreeFrequency_freeFrequencyPart_of_subset`).

Fix all coordinates in $J$ to $+1$, and let $g$ be the restriction of the original sign-valued function to the remaining free coordinates. Because the function depends only on $J$, every restriction obtained by fixing coordinates outside $J$ agrees with this same real-valued function of the free coordinates. Indeed, when comparing two such restrictions, their inputs agree on every coordinate in $J`, as follows from the free-coordinate rule for combining the cubes (`combineSignCube_apply_free`), so dependence on $J$ forces their outputs to agree.

Now express the ambient Fourier coefficient at $S$ as the expectation, over fixed-coordinate assignments on $J$, of the restricted Fourier coefficient at $A` (`expect_restrictionFourierCoeff`), using that the lift of $A$ is $S$. Every term in this expectation is the same indexed Fourier coefficient of the real-valued version of $g$, by the restriction agreement just established. Thus the ambient coefficient equals that indexed coefficient. It is nonzero, so the lower bound for a nonzero Fourier coefficient of a sign-valued function on a finite indexed sign cube applies (`one_div_card_le_abs_indexedFourierCoeff_toReal_of_ne_zero`). The free cube on $J$ has $2^{|J|}$ elements; substituting this cardinality into the bound and using the equality of coefficients gives $2^{-|J|}\le |\widehat f(S)|$.

**Key facts.** `FABL.dependsOn_toReal_iff`, `FABL.fourierCoeff_eq_zero_of_dependsOn_of_not_subset`, `FABL.liftFreeFrequency_freeFrequencyPart_of_subset`, `FABL.combineSignCube_apply_free`, `FABL.expect_restrictionFourierCoeff`, `FABL.one_div_card_le_abs_indexedFourierCoeff_toReal_of_ne_zero`.

**Caveat.** The supplied informal statement describes a learning algorithm, but the formal statement and proof source establish the Fourier-coefficient lower bound stated here.
