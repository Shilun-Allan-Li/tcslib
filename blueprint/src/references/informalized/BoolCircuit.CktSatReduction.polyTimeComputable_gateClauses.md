<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReduction.lean :: BoolCircuit.CktSatReduction.polyTimeComputable_gateClauses -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Gate-Clause Generation

**Claim.** The function that maps a bit string to the clauses emitted by the gate-clause construction is computable in polynomial time.

**Proof.** The emitter machine `emTM` computes the gate-clause function on every input in time $200(n+1)^2$, where $n$ is the input length (`emTM_computes`). This is a polynomial time bound, so the machine and this bound witness polynomial-time computability.

**Key facts.** `BoolCircuit.CktSatReduction.Emitter.emTM_computes`.
