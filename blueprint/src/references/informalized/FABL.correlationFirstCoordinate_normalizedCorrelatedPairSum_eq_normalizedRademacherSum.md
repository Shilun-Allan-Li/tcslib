<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.correlationFirstCoordinate_normalizedCorrelatedPairSum_eq_normalizedRademacherSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Coordinate as a Normalized Sign Sum

**Claim.** For every natural number $n$ and every sign vector $x$ of length $n$, the first coordinate of the normalized correlated sum formed from a pair whose first component is $x$ equals the normalized Rademacher sum of $x$, namely $(\sqrt n)^{-1}\sum_{i=1}^n x_i$, with signs interpreted as real numbers.

**Proof.** The first-coordinate formula for the normalized pair sum gives $(\sqrt n)^{-1}\sum_i\operatorname{signValue}(x_i)$. By definition, the normalized Rademacher sum is $\sum_i (\sqrt n)^{-1}\operatorname{signValue}(x_i)$. Distributing the constant factor across the finite sum identifies these expressions.

**Key facts.** `FABL.correlationFirstCoordinate_normalizedCorrelatedPairSum`.
