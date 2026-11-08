<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductSmallBiasSeed_apply_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seed output and work specification

**Claim.** For each input, Boolean seed, and coordinate, the seed's coordinate agrees with the executable generator on the two field elements decoded from the seed bits, and the work to compute that output bit is at most $16(i+1)(\ell+1)^2$, where $i$ is the coordinate index and $\ell$ is the field degree.

**Proof.** The field degree of the input is positive (\texttt{FABL.SmallBiasInput.fieldDegree_pos}), so the executable output-bit specification applies. That specification states both that the computed bit equals the corresponding coordinate of the executable generator and that its work is at most $16(i+1)(\ell+1)^2$. Apply it to the two field elements obtained by decoding the Boolean seed; the definition of the seed gives exactly this output-bit computation, yielding both conjuncts.

**Key facts.** `FABL.SmallBiasInput.fieldDegree_pos`, `FABL.executableSmallBiasOutputBit_spec`.
