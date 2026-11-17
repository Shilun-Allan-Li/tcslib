<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.majorityThreeValue_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of three-sign majority

**Claim.** With $-1<1$ and the coordinatewise order on triples, three-sign majority is monotone: increasing any coordinates cannot decrease its output.

**Proof.** The general monotonicity theorem for majority (`majority_monotone`) states that the majority function is monotone for every number of coordinates. Specializing it to three coordinates gives the asserted monotonicity.

**Key facts.** `FABL.majority_monotone`.
