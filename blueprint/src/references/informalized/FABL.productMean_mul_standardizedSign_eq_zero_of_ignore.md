<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productMean_mul_standardizedSign_eq_zero_of_ignore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Mean Under Coordinate Independence

**Claim.** If $h$ is unchanged when coordinate $i$ is replaced by any sign, then under the product distribution of independent biased signs, the mean of $h(x)$ times the standardized sign in coordinate $i$ is zero.

**Proof.** Let $q(x)=h(x)$ times the standardized sign in coordinate $i$. First replace $q$ by its projection onto all coordinates except $i$. This preserves its product mean, by the coordinate-projection mean identity (`FiniteFourierBasis.productMean_projectOnCoordinates`). At a fixed input $x$, that projection is the expectation over a fresh sign $\omega$ of $q$ evaluated after replacing coordinate $i$ by $\omega$ (`coordinateProjection_apply`). The hypothesis makes the $h$ factor equal to $h(x)$ throughout this average, while the standardized-sign factor becomes the standardized sign of $\omega$. Thus the average is $h(x)$ times the one-coordinate mean of the standardized sign. That one-coordinate mean is zero (`pmfExpectation_biasedStandardizedSign`), so the projection vanishes at every input. Its product mean is consequently zero, using that the mean of the zero function is zero (`pmfExpectation_const`), and the original product mean is zero as well.

**Key facts.** `FABL.FiniteFourierBasis.productMean_projectOnCoordinates`, `FABL.coordinateProjection_apply`, `FABL.pmfExpectation_biasedStandardizedSign`, `FABL.pmfExpectation_const`.
