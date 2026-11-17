<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEval.lean :: BoolCircuit.CVALPrefix_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Circuit Evaluation Is in Polynomial Time

**Claim.** The language of paired encodings of a circuit and input satisfying the stated prefix-evaluation conditions is decidable in polynomial time by a finite-state multitape Turing machine.

**Proof.** The circuit-evaluation machine has a quadratic running-time bound, and the verdict characterization says that it accepts exactly the strings in the prefix-evaluation language. Applying the polynomial-time membership characterization with constants $12$ and degree $2$ gives membership in polynomial time.

**Key facts.** `Complexity.mem_P_iff`, `BoolCircuit.CircuitEval.decidesInTime_of_verdict`, `BoolCircuit.mem_CVALPrefix_iff`.
