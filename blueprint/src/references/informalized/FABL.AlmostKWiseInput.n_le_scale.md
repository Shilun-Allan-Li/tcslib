<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.AlmostKWiseInput.n_le_scale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension bounded by the scale

**Claim.** The output dimension is at most the scale defined as the least natural number whose product with the numerator is at least the output dimension times the denominator.

**Proof.** Regard the input’s dimension, numerator, and denominator as a small-bias input. Its required positivity and bias hypotheses are inherited from the given input. The small-bias scale bound (in `FABL.SmallBiasInput.n_le_scale`) says that its dimension is at most its scale. Since this scale is exactly the scale defined for the original input, the desired inequality follows.

**Key facts.** `FABL.AlmostKWiseInput.n_pos`, `FABL.SmallBiasInput.n_le_scale`.
