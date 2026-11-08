<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.adderCircuit_size_three_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adder Size at Multiples of Three

**Claim.** For every natural number $k$, the adder circuit on $3k$ input vertices has size $18k+4$.

**Proof.** The general size formula gives size $3k+15((3k)/3)+4$. Since $(3k)/3=k$, this simplifies to $18k+4$.

**Key facts.** `BoolCircuit.adderCircuit_size`.
