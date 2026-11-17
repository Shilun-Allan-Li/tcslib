<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LearningModel.lean :: FABL.SparseFourierHypothesis.value_cast_eq_realValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rational and real Fourier values agree

**Claim.** For every sign vector, the rational Fourier sum of a sparse Fourier hypothesis, regarded as real, equals its real Fourier sum.

**Proof.** Expand both values and the sign monomials. The inclusion of rational numbers into the reals preserves finite sums, products, and the signs at each coordinate. Thus each rational summand, after casting to the reals, is exactly the corresponding real summand, and the finite sums agree.
