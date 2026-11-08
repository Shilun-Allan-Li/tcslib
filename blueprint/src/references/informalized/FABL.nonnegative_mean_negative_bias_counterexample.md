<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdBias.lean :: FABL.nonnegative_mean_negative_bias_counterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Bias with Nonnegative Mean

**Claim.** There exist a Boolean function on the one-dimensional cube, a negative constant term, and a linear coefficient such that the function is the threshold sign of the resulting affine form at every input, while its mean is nonnegative.

**Proof.** Choose the coordinate dictator, take constant term −1/2, and take the sole linear coefficient to be 1. At the two possible inputs, the affine form is −3/2 when the coordinate is −1 and 1/2 when it is 1. Its threshold sign is accordingly −1 or 1, exactly the dictator's value. For the mean, the real-valued dictator agrees with the monomial indexed by the singleton coordinate (`dictator_toReal_eq_monomial_singleton`). The expectation of a monomial is zero for any nonempty index set (`expect_monomial`); this singleton is nonempty, so the mean is zero and in particular nonnegative.

**Key facts.** `FABL.dictator_toReal_eq_monomial_singleton`, `FABL.expect_monomial`.
