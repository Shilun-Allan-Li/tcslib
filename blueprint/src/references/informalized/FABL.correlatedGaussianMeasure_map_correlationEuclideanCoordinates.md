<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.correlatedGaussianMeasure_map_correlationEuclideanCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Euclidean correlated Gaussian law

**Claim.** For $-1<\rho<1$, the law of the pair obtained from independent standard Gaussians by $X=U$ and $Y=\rho U+\sqrt{1-\rho^2}V$, expressed in Euclidean coordinates, is the multivariate Gaussian with mean $(0,0)$ and covariance matrix $\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix}$.

**Proof.** We identify the characteristic functions of the two measures. Fix a Euclidean test vector $t$. By the change-of-variables formula for integrating against a mapped measure, the characteristic function of the Euclidean-coordinate image is the characteristic function of the original correlated measure evaluated at the corresponding plane vector; the equality of inner products under the coordinate identifications is given by `inner_correlationEuclideanCoordinates`. The characteristic function of the correlated measure is $\exp(-Q_\rho(s)/2)$, where $Q_\rho$ is its quadratic form (`charFun_correlatedGaussianMeasure`). The matrix $\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix}$ is positive definite when $-1<\rho<1$ (`correlationMatrix_posDef`), so the characteristic-function formula for a multivariate Gaussian applies. Its exponent is the negative one-half of the matrix quadratic form in $t$. The identity between this matrix quadratic form and $Q_\rho$ in Euclidean coordinates is `correlationQuadraticForm_euclideanCorrelationCoordinates`; expanding the two expressions gives equality. Thus the measures have identical characteristic functions, and uniqueness of characteristic functions gives the claimed equality.

**Key facts.** `FABL.continuous_correlationEuclideanCoordinates`, `FABL.inner_correlationEuclideanCoordinates`, `FABL.charFun_correlatedGaussianMeasure`, `FABL.correlationMatrix_posDef`, `FABL.correlationQuadraticForm_euclideanCorrelationCoordinates`.
