<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.sealTriple_acyclic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of the sealing gates

**Claim.** When $u<N$ and $o<N$, the three gates in the sealing triple are acyclic relative to $N$.

**Proof.** Unpack acyclicity one gate at a time (`gatesAcyclic_cons`). The NOT gate is at position $0$ and reads only $u<N$. The OR gate is at position $1$ and reads $u$ and $N$, both below $N+1$. The AND gate is at position $2$ and reads $o$ and $N+1$, both below $N+2$. These are exactly the required bounds; the empty remainder contributes no conditions (`gatesAcyclic_nil`).

**Key facts.** `BoolCircuit.gatesAcyclic_cons`, `BoolCircuit.gatesAcyclic_nil`.
