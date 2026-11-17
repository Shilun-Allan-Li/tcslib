<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.value_yleaf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values of the First-Level Leaves

**Claim.** For $p<2^{n-k}$, the indicated first-level leaf has value true exactly when the heap path of $x$ from offset $0$ at depth $n-k$ is $2^{n-k}+p$.

**Proof.** Apply the heap-value theorem (`BoolCircuit.Lupanov.value_heap`) to the first heap, whose base position is $n$, offset is $0$, and depth is $n-k$. The gate identification needed by that theorem is supplied by the fact that positions in this block are precisely the corresponding heap gates (`BoolCircuit.Lupanov.gateAt_y`). The offset identities (`BoolCircuit.Lupanov.offsets`) and the identity $2^{a+1}=2\cdot 2^a$ (`BoolCircuit.Lupanov.two_pow_succ_eq`) verify that the block is long enough and that the chosen index is valid. The heap-value theorem gives the desired path comparison with depth $\log_2(2^{n-k}+p)$. Since $p<2^{n-k}$, this logarithm equals $n-k$ (`BoolCircuit.Lupanov.log_two_pow_add`), yielding the claim.

**Key facts.** `BoolCircuit.Lupanov.offsets`, `BoolCircuit.Lupanov.two_pow_succ_eq`, `BoolCircuit.Lupanov.gateAt_y`, `BoolCircuit.Lupanov.value_heap`, `BoolCircuit.Lupanov.log_two_pow_add`.
