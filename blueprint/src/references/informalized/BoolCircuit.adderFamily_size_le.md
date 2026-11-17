<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/AdderLanguage.lean :: BoolCircuit.adderFamily_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adder Circuit Size Bound

**Claim.** For every natural number $n$, the size of the adder family circuit on inputs of length $n$ is at most $6n+4$.

**Proof.** Unfold the family’s definition and split on whether $n$ is divisible by three. In the divisible case, the circuit is the adder circuit, whose size is $n+15(n/3)+4$ (`BoolCircuit.adderCircuit_size`). Since $n/3$ here is an integer quotient with $n=3(n/3)$, this expression equals $6n+4$. In the other case, the circuit is constant and has size $n+1$ (`BoolCircuit.constCircuit_size`), which is at most $6n+4$ for every natural number $n$.

**Key facts.** `BoolCircuit.adderCircuit_size`, `BoolCircuit.constCircuit_size`.
