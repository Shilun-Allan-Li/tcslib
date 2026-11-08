<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.mean_pointSubcubeIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Point Indicator

**Claim.** For every nonnegative integer \(k\), the function that is one at the all-\(+1\) point of the \(k\)-dimensional sign cube and zero elsewhere has mean \(2^{-k}\).

**Proof.** On a finite space with the uniform distribution, the mean is the sum of the function's values divided by the number of points. The indicator contributes exactly one to this sum, since only the all-\(+1\) point has value one. The cube has \(2^k\) points, so the mean is \(1/2^k\).
