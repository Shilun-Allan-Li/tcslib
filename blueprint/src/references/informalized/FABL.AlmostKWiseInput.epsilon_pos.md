<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.AlmostKWiseInput.epsilon_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the bias

**Claim.** For an input with positive bias numerator and denominator satisfying twice the numerator at most the denominator, the associated bias is positive.

**Proof.** The input’s associated small-bias data has the same numerator and denominator, and its bias therefore agrees with the input’s bias. The positivity result for small-bias inputs (in `FABL.SmallBiasInput.epsilon_pos`) now gives the claim.

**Key facts.** `FABL.SmallBiasInput.epsilon_pos`.
