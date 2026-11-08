<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Lupanov.lean :: BoolCircuit.Lupanov.lupGates_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of the appended OR tree

**Claim.** For $k\le n$, appending the OR tree to the prescribed Lupanov gate list yields an acyclic extension with a valid output vertex whose value is the disjunction of the combining-root values. Its length and output depth satisfy the stated bounds, and every appended gate has at most two distinct inputs.

**Proof.** Apply the specification for emitting a tree of gates to the combining roots and the original Lupanov gate list. Its hypotheses hold because OR is not NOT, the original gates are acyclic (`gates_acyclic`), and every root is a valid vertex of that list. For the last condition, write a root as $n+o_C+p$ with $p<2^{n-k}$; the length of the original list is $T=o_C+2^{n-k}$ by `length_gates` and `offsets`, so the root is below $n+T$. The emitted-tree specification (`emitTree_spec`) now gives the acyclic extension, valid output, value, length, depth, and appended-gate properties. The remaining root calculation uses the offset identities to establish the required inequality.

**Key facts.** `BoolCircuit.Lupanov.gates_acyclic`, `BoolCircuit.Lupanov.length_gates`, `BoolCircuit.Lupanov.offsets`, `BoolCircuit.emitTree_spec`.
