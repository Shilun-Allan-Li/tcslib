<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.value_func -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values of Function Gates

**Claim.** For every $t<2^{2^k}$, the value at vertex $n+o_F(n,k)+t$ is digit $H_x(n-k,k)-2^k$ of $t$.

**Proof.** The proof uses strong induction on $t$, so the value at a gate can be reduced to an earlier function gate. The bounds on heap paths (heapPath_bounds) and the block offsets (offsets) provide the index bounds needed to apply the gate and leaf evaluation results. The gate-position evaluation principle and the description of a function-block gate (value_gateAt, gateAt_f) reduce the desired value to the evaluation of that gate. When $t=0$, the function gate has no inputs and evaluates to false, matching the zeroth number's digit. For $t>0$, put $L=\lfloor\log_2 t\rfloor$. The defining properties of the logarithm give $2^L\le t<2^{L+1}$, and the assumed bound on $t$ gives $L<2^k$. The gate is an OR of the earlier function gate indexed by $t-2^L$ and the corresponding heap leaf. By the induction hypothesis, the earlier gate's value is digit $H_x(n-k,k)-2^k$ of $t-2^L$; the leaf's value is true exactly when the relevant heap-path digit equals $L$ (value_zleaf). The path bounds show that this digit position is precisely the one in the claim. Since $t=2^L+(t-2^L)$ with $t-2^L<2^L$, the binary-digit addition rule says digit $r$ of $t$ is the disjunction of digit $r$ of $t-2^L$ and the condition $r=L$ (testBit_two_pow_add_of_lt). Thus the OR gate has exactly the claimed value.

**Key facts.** `BoolCircuit.Lupanov.heapPath_bounds`, `BoolCircuit.Lupanov.offsets`, `BoolCircuit.Lupanov.value_gateAt`, `BoolCircuit.Lupanov.gateAt_f`, `BoolCircuit.Lupanov.testBit_two_pow_add_of_lt`, `BoolCircuit.Lupanov.two_pow_succ_eq`, `BoolCircuit.Lupanov.value_zleaf`.
