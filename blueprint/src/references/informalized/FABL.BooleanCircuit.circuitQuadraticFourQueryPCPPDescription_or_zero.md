<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticFourQueryPCPPDescription_or_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Four-Query PCPP or Zero-Input Case

**Claim.** Either the circuit has zero input bits and accepts every assignment or rejects every assignment, or its accepted-input property has a PCPP description for some positive input length.

**Proof.** Split into the cases that the number of input bits is zero or nonzero. In the zero case, the result for circuits with no input bits gives the universal-acceptance or universal-rejection alternative. In the nonzero case, that number is positive, so it supplies the nonzero witness required for the existential claim; the circuit’s four-query PCPP description supplies the description for its accepted-input property.

**Key facts.** `FABL.BooleanCircuit.acceptedProperty_zero_universal_or_empty`.
