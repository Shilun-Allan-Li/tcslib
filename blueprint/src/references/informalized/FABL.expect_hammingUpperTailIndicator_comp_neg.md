<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.expect_hammingUpperTailIndicator_comp_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of a Rademacher Tail

**Claim.** For every real threshold and every dimension, the uniform expected tail indicator of the normalized Rademacher sum evaluated at $-x$ equals its expected value at $x$.

**Proof.** Negation is a bijection of the sign cube, with itself as inverse. Reindex the expectation over $x$ by this bijection; the input $-x$ then becomes the new assignment, and the integrand is the tail indicator at that assignment. Since a bijection preserves the uniform average, the two expectations are equal.
