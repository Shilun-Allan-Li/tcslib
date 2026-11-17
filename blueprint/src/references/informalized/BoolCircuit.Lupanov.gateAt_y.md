<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.gateAt_y -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First heap block gate formula

**Claim.** If $1\le q<2^{n-k+1}$, the gate at index $n+(q-1)$ is the heap gate with parameters $n$, base $2n$, offset $0$, and size $q$.

**Proof.** By the offset identity for $o_Z$ and the power identity $2^{a+1}=2\cdot2^a$ (`two_pow_succ_eq`), the bound on $q$ implies $n+(q-1)<o_Z(n,k)$. Since $q\ge1$, this index is at least $n$, so it is not in the input block. The circuit definition therefore selects the first heap block. Its size parameter is $(n+(q-1))-n+1=q$, giving the stated heap gate.

**Key facts.** `BoolCircuit.Lupanov.offsets`, `BoolCircuit.Lupanov.two_pow_succ_eq`.
