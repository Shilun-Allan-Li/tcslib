<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableauCorrect.lean :: Complexity.exists_tableau_circuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit simulation of an oblivious computation

**Claim.** An oblivious finite machine deciding L within time T has, for each input length n, a well-formed fan-in-two Boolean circuit of size linear in T(n)+n+1 that computes the indicator of L.

**Proof.** For each n, take the tableau circuit for M on inputs of length n and time horizon T(n). Its fan-in-two well-formedness is given by `tableauCircuit_isFaninTwo`, and its evaluation on every n-bit input agrees with M’s decision by `tableauCircuit_eval_of_decidesInTime`, using obliviousness and the time-bounded decider hypothesis. Its size is n+2+(T(n)+1)·tableauWidth(M), by `tableauCircuit_size`. Taking K=tableauWidth(M)+2 bounds this expression by K(T(n)+n+1), yielding the claimed family of circuits.

**Key facts.** `Complexity.tableauCircuit_isFaninTwo`, `Complexity.tableauCircuit_eval_of_decidesInTime`, `Complexity.tableauCircuit_size`.
