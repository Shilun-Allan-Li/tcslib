<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.variance_monotonization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance Under Coordinate Monotonization

**Claim.** Coordinate monotonization of a Boolean function preserves the variance of its real-valued version.

**Proof.** For a Boolean-valued function, the variance equals one minus the square of its mean; this follows from the variance formula in `variance_eq_four_mul_probabilities`. The mean is unchanged by monotonization (`mean_monotonization`). Substituting this common mean into the variance formula for the original function and its monotonization gives equal variances.

**Key facts.** `FABL.variance_eq_four_mul_probabilities`, `FABL.mean_monotonization`.
