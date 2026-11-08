<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.value_comb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Combining Gate

**Claim.** For every $p<2^{n-k}$, the value at vertex $n+o_C(n,k)+p$ is the conjunction of the condition that the initial heap path equals $2^{n-k}+p$ and the specified digit of the code of $f$.

**Proof.** First, the offsets of the gate blocks ensure that the vertex in question corresponds to gate position $o_C(n,k)+p$. The gate-position evaluation principle identifies its value with the evaluation of that gate on the circuit's value list (value_gateAt). The gate at that position is the combining gate with the prescribed two inputs (gateAt_c), and a two-input AND gate evaluates to the conjunction of the values at those inputs (eval_and_pair). The first input is the leaf for the initial heap path, whose value is the equality test that this path equals $2^{n-k}+p$ (value_yleaf). For the second input, the code is an encoding of a Boolean list of length $2^k$, hence is below $2^{2^k}$ by the encoding bound (ofBits_lt). The function-gate value formula therefore applies and identifies this input's value with the indicated digit of the code (value_func). Combining the two input values proves the claim.

**Key facts.** `BoolCircuit.Lupanov.value_gateAt`, `BoolCircuit.Lupanov.gateAt_c`, `BoolCircuit.Lupanov.eval_and_pair`, `BoolCircuit.Lupanov.value_yleaf`, `BoolCircuit.Lupanov.ofBits_lt`, `BoolCircuit.Lupanov.value_func`.
