<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.SmallBiasFourierInput.sampleCount_le_four_mul_scale_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sample count upper bound

**Claim.** The sample count is at most four times the square of the associated generator input's scale.

**Proof.** The sample count is the square of $2$ raised to the field degree. The field-size bound gives $2^{\mathrm{fieldDegree}}\le 2\,\mathrm{scale}$ (`SmallBiasInput.fieldSize_le_two_scale`). Multiplying this inequality by itself yields a bound by $(2\,\mathrm{scale})^2$, which equals $4\,\mathrm{scale}^2$.

**Key facts.** `FABL.SmallBiasInput.fieldSize_le_two_scale`.
