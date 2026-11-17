<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Lupanov.lean :: BoolCircuit.Lupanov.lupDAG_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for the constructed circuit

**Claim.** For every Boolean function $f$ on $n$ bits and every $k\le n$, the constructed circuit has size at most $2n+4\cdot2^{n-k}+2\cdot2^k+2^{2^k}$.

**Proof.** The tree construction adds at most the tree cost of the number of combining roots to the original gate count, by the length bound in `lupGates_spec`. There are $2^{n-k}$ roots, so their tree cost is $2^{n-k}-1$. The original gate list has length $T=o_C+2^{n-k}$, by `length_gates` and the offset identities `offsets`. Consequently the circuit size, which is $n$ plus the resulting gate-list length, is at most $n+T+(2^{n-k}-1)$. Substituting $o_C=o_F+2^{2^k}$ and $o_F+1=o_Z+2\cdot2^k$, then $o_Z+1=n+2\cdot2^{n-k}$, simplifies this bound to the stated expression.

**Key facts.** `BoolCircuit.Lupanov.lupGates_spec`, `BoolCircuit.Lupanov.offsets`, `BoolCircuit.Lupanov.length_gates`.
