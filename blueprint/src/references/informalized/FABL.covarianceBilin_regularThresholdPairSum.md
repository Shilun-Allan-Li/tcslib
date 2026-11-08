<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.covarianceBilin_regularThresholdPairSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Covariance of a Regular Correlated Pair Sum

**Claim.** For $\rho\in[-1,1]$ and coefficients satisfying $\sum_i a_i^2=1$, the covariance bilinear form of the regular correlated pair sum is represented by the matrix $\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix}$.

**Proof.** Write $Z$ for the random pair sum. Its summands have finite third moments, hence the sum has a finite second moment, so the covariance of its projections is computed by their centered products. The sum has mean zero (`FABL.integral_regularThresholdPairSum_eq_zero`), so for vectors $x,y$ this covariance is the expectation of $\langle x,Z\rangle\langle y,Z\rangle$. Expanding these two inner products separates the expectation into four terms, with coefficients $x_0y_0,x_0y_1,x_1y_0,x_1y_1$, multiplying respectively the products of the first coordinates, the two cross-products, and the product of the second coordinates.

The first-coordinate square has expectation $\sum_i a_i^2$: its marginal is uniform (`FABL.pmfExpectation_correlatedPairPMF_fst`), uniform expectation agrees with cube expectation (`FABL.pmfExpectation_uniformPMF_eq_expect`), and the second moment of a linear form is the sum of squared coefficients (`FABL.expect_linearForm_sq`). The same reasoning for the second marginal gives the same value (`FABL.pmfExpectation_correlatedPairPMF_snd`). The mixed product has expectation $\rho\sum_i a_i^2$ (`FABL.pmfExpectation_correlatedPairPMF_linearForm_mul`); reversing its factors does not change it. Passing between the finite probability expectation and its integral uses `FABL.pmfExpectation_eq_integral`.

Linearity of expectation (`FABL.pmfExpectation_add`, `FABL.pmfExpectation_const_mul`) now yields the four-term expression. Using $\sum_i a_i^2=1$, its diagonal coefficients are $x_0y_0$ and $x_1y_1$, and its cross coefficients are $\rho x_0y_1$ and $\rho x_1y_0$. This is exactly $x^{\mathsf T}\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix}y$.

**Key facts.** `FABL.integral_regularThresholdPairSum_eq_zero`, `FABL.pmfExpectation_correlatedPairPMF_fst`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_linearForm_sq`, `FABL.pmfExpectation_correlatedPairPMF_snd`, `FABL.pmfExpectation_correlatedPairPMF_linearForm_mul`, `FABL.pmfExpectation_eq_integral`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const_mul`.
