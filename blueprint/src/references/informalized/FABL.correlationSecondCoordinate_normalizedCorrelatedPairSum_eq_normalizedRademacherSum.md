<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.correlationSecondCoordinate_normalizedCorrelatedPairSum_eq_normalizedRademacherSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Coordinate of the Pair Sum

**Claim.** For every $n$ and sign vectors $x,y\in\{-1,1\}^n$, the second coordinate of their normalized correlated sum is the normalized Rademacher sum of $y$.

**Proof.** The second-coordinate formula for the normalized correlated pair sum (`FABL.correlationSecondCoordinate_normalizedCorrelatedPairSum`) identifies that coordinate with $(\sqrt n)^{-1}\sum_i\operatorname{signValue}(y_i)$. Expanding the definition of the normalized Rademacher sum gives $\sum_i (\sqrt n)^{-1}\operatorname{signValue}(y_i)$. Since the scalar factor is constant in $i$, this is the same expression.

**Key facts.** `FABL.correlationSecondCoordinate_normalizedCorrelatedPairSum`.
