<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.gateAt_faninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in bound for circuit gates

**Claim.** For $k\le n$ and any gate index $j$ below the total number of gates, the gate at index $j$ is well formed and reads at most two vertices.

**Proof.** Use the block-size identities and $2^{a+1}=2\cdot2^a$ to divide into the five cases in the definition of the circuit. An input gate is a negation with one argument, so it is well formed and has fan-in at most two. In either heap block, the gate is empty when its size parameter is at most one; otherwise it has two arguments. The logarithmic bound `log_le_of_lt_two_pow_succ` and the bound `litV_le` give the needed inequalities on the argument indices, which in particular show that the two entries are distinct. In the function block, the zero-parameter gate is empty. Otherwise `Nat.log_lt_of_lt_pow` and the block bound give $\log_2 t<2^k$; the two argument formulas then yield distinct entries. The final combination gate has two arguments, and its block bounds likewise show they are distinct. The empty-gate fact (`nil_faninTwo`) and the two-entry fact (`pair_faninTwo`) supply well-formedness and the fan-in bound in the respective cases.

**Key facts.** `BoolCircuit.Lupanov.two_pow_succ_eq`, `BoolCircuit.Lupanov.nil_faninTwo`, `BoolCircuit.Lupanov.log_le_of_lt_two_pow_succ`, `BoolCircuit.Lupanov.litV_le`, `BoolCircuit.Lupanov.pair_faninTwo`.
