<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.sealTriple_strict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strictness of the sealing gates

**Claim.** Each gate in the sealing triple has distinct arguments, with one argument for the NOT gate and two for each of the OR and AND gates.

**Proof.** A member of the triple is one of its three displayed gates. The NOT gate has the singleton argument list $[u]$, and the OR gate has arguments $[u,N]$, distinct because $u<N$. The AND gate has arguments $[o,N+1]$, distinct because $o<N<N+1$. In each case the argument count matches the gate kind, proving strictness.
