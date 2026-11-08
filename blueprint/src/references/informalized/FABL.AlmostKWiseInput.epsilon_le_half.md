<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.AlmostKWiseInput.epsilon_le_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound on the bias

**Claim.** For an input with positive bias numerator and denominator satisfying twice the numerator at most the denominator, the associated bias is at most one half.

**Proof.** The input’s associated small-bias data has the same numerator and denominator, so its bias is the same real number. Applying the upper bound on the bias for small-bias inputs (in `FABL.SmallBiasInput.epsilon_le_half`) gives the result.

**Key facts.** `FABL.SmallBiasInput.epsilon_le_half`.
