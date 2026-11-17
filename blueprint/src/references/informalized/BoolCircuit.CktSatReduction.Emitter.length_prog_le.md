<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec.lean :: BoolCircuit.CktSatReduction.Emitter.length_prog_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate program length bound

**Claim.** For each Boolean gate kind and each code in the three-element set, the instruction program encoding that gate has length at most $56$.

**Proof.** Split into the three gate kinds and the three possible codes. In each of the resulting nine cases, the definitions of the code’s argument list, the gate’s Tseitin clauses, and the program encoding reduce the program to a concrete finite list. Counting its instructions verifies the bound in every case.
