<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.value_zleaf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values of the Second-Level Leaves

**Claim.** For $r<2^k$, the indicated second-level leaf has value true exactly when the heap path of $x$ from offset $n-k$ at depth $k$ is $2^k+r$.

**Proof.** Apply the heap-value theorem (`BoolCircuit.Lupanov.value_heap`) to the second heap, with base position $o_Z(n,k)$, offset $n-k$, and depth $k$. Positions in this block are the corresponding second-level heap gates (`BoolCircuit.Lupanov.gateAt_z`). The offset identities (`BoolCircuit.Lupanov.offsets`) and $2^{a+1}=2\cdot 2^a$ (`BoolCircuit.Lupanov.two_pow_succ_eq`) establish the block bounds required for that theorem. It gives the path comparison at depth $\log_2(2^k+r)$; the inequality $r<2^k$ makes this logarithm $k$ (`BoolCircuit.Lupanov.log_two_pow_add`).

**Key facts.** `BoolCircuit.Lupanov.offsets`, `BoolCircuit.Lupanov.two_pow_succ_eq`, `BoolCircuit.Lupanov.gateAt_z`, `BoolCircuit.Lupanov.value_heap`, `BoolCircuit.Lupanov.log_two_pow_add`.
