<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.correlationSecondCoordinate_normalizedCorrelatedPairSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second coordinate of a normalized pair sum

**Claim.** For every natural number $n$ and every pair $x,y\in\{-1,1\}^n$ of sign vectors, the second coordinate of their normalized correlated sum is $(\sqrt n)^{-1}\sum_{i=1}^n y_i$.

**Proof.** Each correlated sign vector has second coordinate equal to the value of its second sign. The second coordinate of a sum is the sum of the second coordinates, and scalar multiplication multiplies that coordinate by the same scalar. Applying these coordinatewise facts to the normalized sum gives $(\sqrt n)^{-1}$ times the sum of the second signs. Under the identification of the pair of sign vectors with its coordinatewise pairs, those second signs are precisely the entries $y_i$, proving the formula.
