<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.gateAt_z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second heap block gate formula

**Claim.** If $1\le q<2^{k+1}$, the gate at index $o_Z(n,k)+(q-1)$ is the heap gate with parameters $n$, base $n+o_Z(n,k)$, offset $n-k$, and size $q$.

**Proof.** The offset identity for $o_F$ and $2^{k+1}=2\cdot2^k$ (`two_pow_succ_eq`) show that the assumed bound places $o_Z(n,k)+(q-1)$ strictly below $o_F(n,k)$. Since $q\ge1$, the index is at least $o_Z(n,k)$, which lies beyond the input and first heap blocks. Thus the circuit definition selects the second heap block. Its size parameter is $(o_Z(n,k)+(q-1))-o_Z(n,k)+1=q$, so the gate is the claimed heap gate.

**Key facts.** `BoolCircuit.Lupanov.offsets`, `BoolCircuit.Lupanov.two_pow_succ_eq`.
