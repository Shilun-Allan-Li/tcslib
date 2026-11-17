<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Lupanov.lean :: BoolCircuit.exists_dagCircuit_faninTwo_size_le_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small fan-in-two circuit representation

**Claim.** For every Boolean function on $n$ input bits, there is a well-formed acyclic Boolean circuit with at most two inputs per gate computing the function and having size at most $40\cdot 2^n/(n+1)$.

**Proof.** First take a circuit whose fan-in and well-formedness are as required, which computes the function and satisfies $(n+1)\,\mathrm{size}(C)\le 40\cdot 2^n$ (`BoolCircuit.exists_dagCircuit_faninTwo_mul_size_le`). Since $n+1$ is positive, division with remainder gives the equivalent implication that $\mathrm{size}(C)\le 40\cdot 2^n/(n+1)$. The same circuit therefore has the claimed size bound.

**Key facts.** `BoolCircuit.exists_dagCircuit_faninTwo_mul_size_le`.
