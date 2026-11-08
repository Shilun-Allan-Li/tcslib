<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PUniformP.lean :: BoolCircuit.DAGCircuitFamily.IsPUniform.language_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform circuit language is in P

**Claim.** If a circuit family is polynomial-time-uniform and each circuit is well formed with at most two inputs per gate, then the language accepted by the family belongs to P.

**Proof.** The polynomial-time-uniformity and fan-in hypotheses give a polynomial-time many-one reduction from the family's accepted language to the Boolean circuit value language (BoolCircuit.DAGCircuitFamily.IsPUniform.polyTimeReducible_CVAL). The Boolean circuit value language is in P (BoolCircuit.CVAL_mem_P). Polynomial-time many-one preimages of languages in P are also in P (Complexity.mem_P_of_polyTimeReducible). Applying this closure result to the reduction proves that the family's language is in P.

**Key facts.** `BoolCircuit.DAGCircuitFamily.IsPUniform.polyTimeReducible_CVAL`, `BoolCircuit.CVAL_mem_P`, `Complexity.mem_P_of_polyTimeReducible`.
