<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec.lean :: BoolCircuit.CktSatReduction.Emitter.serialize_eq_serBody -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Formula serialization decomposition

**Claim.** The binary serialization of every CNF formula is its clause-body serialization followed by one final false bit.

**Proof.** Both sides reduce directly from their definitions: the formula serialization is the flat-map of the clause encodings followed by a false bit, and the clause-body serialization is precisely that flat-map. Hence the lists are equal.
