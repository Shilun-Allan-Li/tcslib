<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.coe_normalizedCorrelatedSignSumMeasure_upperRight_eq_noiseStability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper-Right Quadrant and Noise Stability

**Claim.** The probability that both coordinates of the normalized sum exceed $t$ equals the noise stability at correlation $\rho$ of the indicator that a normalized sum of uniform signs exceeds $t$.

**Proof.** Write the quadrant probability as the integral of its indicator. The normalized correlated sign sum measure is the pushforward of the correlated-pair distribution by the normalized-sum map (\texttt{normalizedCorrelatedSignSumMeasure\_eq\_map\_correlatedPairPMF}); the quadrant is open, so its indicator is measurable, and the pushforward integration formula changes this to an integral over correlated input pairs. Convert that integral to the finite expectation defining noise stability by the finite-distribution expectation formula (\texttt{pmfExpectation\_eq\_integral}). Now fix a pair $(x,y)$. The first coordinate of its normalized sum is the normalized Rademacher sum of $x$ (\texttt{correlationFirstCoordinate\_normalizedCorrelatedPairSum\_eq\_normalizedRademacherSum}), and the second is the corresponding sum of $y$ (\texttt{correlationSecondCoordinate\_normalizedCorrelatedPairSum\_eq\_normalizedRademacherSum}). Split according to whether each sum exceeds $t$. If both do, the point lies in the upper-right quadrant and both tail indicators equal $1$. In each of the other three cases, at least one coordinate fails the strict threshold, so the point is outside the quadrant and the product of the tail indicators is $0$. The integrands therefore agree for every pair, proving the equality of expectations.

**Key facts.** `FABL.isOpen_gaussianUpperRightQuadrant`, `FABL.normalizedCorrelatedSignSumMeasure_eq_map_correlatedPairPMF`, `FABL.pmfExpectation_eq_integral`, `FABL.correlationFirstCoordinate_normalizedCorrelatedPairSum_eq_normalizedRademacherSum`, `FABL.correlationSecondCoordinate_normalizedCorrelatedPairSum_eq_normalizedRademacherSum`.
