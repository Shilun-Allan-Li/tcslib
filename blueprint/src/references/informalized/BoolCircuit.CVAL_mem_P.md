<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEval.lean :: BoolCircuit.CVAL_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Evaluation Is in Polynomial Time

**Claim.** The language of paired encodings of a fan-in-at-most-two circuit and its input, where the circuit evaluates to true, is decidable in polynomial time by a finite-state multitape Turing machine.

**Proof.** The circuit-evaluation machine decides this language in time at most $12(n+1)^2$ on inputs of length $n$. The polynomial-time membership characterization therefore applies with constant $12$ and degree $2$, proving that the language belongs to polynomial time.

**Key facts.** `Complexity.mem_P_iff`, `BoolCircuit.CircuitEval.evalTM_decidesInTime_CVAL`.
