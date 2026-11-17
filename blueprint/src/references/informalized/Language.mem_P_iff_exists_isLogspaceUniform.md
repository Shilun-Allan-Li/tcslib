<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableau.lean :: Language.mem_P_iff_exists_isLogspaceUniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace-Uniform Circuit Characterization of P

**Claim.** A Boolean language belongs to polynomial time exactly when a fan-in-two, polynomial-size, logspace-uniform Boolean circuit family recognizes it.

**Proof.** If $L$ is in polynomial time, `Language.exists_isLogspaceUniform_of_mem_P` provides a logspace-uniform family of polynomial size and fan-in at most two whose language is $L$. Conversely, suppose such a family $C$ is given. Its logspace uniformity implies polynomial-time uniformity by `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPUniform`. The theorem `Language.mem_P_of_isPUniform` then shows that a polynomial-time-uniform, fan-in-two family recognizing $L$ places $L$ in polynomial time; the size and language hypotheses are exactly those required there.

**Key facts.** `Language.exists_isLogspaceUniform_of_mem_P`, `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPUniform`, `Language.mem_P_of_isPUniform`.
