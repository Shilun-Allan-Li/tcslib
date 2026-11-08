<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.degree_test_accept_prob_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability and Gowers norm

**Claim.** The acceptance probability of the $(d+1)$-fold derivative low-degree test equals one half of one plus the $(d+1)$-st Gowers norm power of the sign lift.

**Proof.** For each base point and direction tuple, the Gowers product of the sign lift is either $1$ or $-1` (`gowers_product_pm1`). Thus the indicator that the test accepts, namely that this product equals $1$, is pointwise $(1+\mathrm{GP})/2$. Averaging this identity over all base points and direction tuples gives one half of $1$ plus the average Gowers product. The latter is exactly the defined Gowers norm power. The constant term averages to $1$, since the number of base points is $2^n$ (`card_hypercube`) and the number of direction tuples is $2^{n(d+1)}$; these cardinalities cancel the normalizing denominators in the expectations.

**Key facts.** `LowDegreeTest.gowers_product_pm1`, `BoolFourier.card_hypercube`.
