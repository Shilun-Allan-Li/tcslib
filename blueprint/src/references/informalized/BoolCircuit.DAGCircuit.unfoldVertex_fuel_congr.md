<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.DAGCircuit.unfoldVertex_fuel_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fuel Independence of Circuit Unfolding

**Claim.** For a well-formed circuit, if vertex $v$ is below both fuel bounds $f$ and $f'$, unfolding it with either bound and the same polarity produces the same tree.

**Proof.** Induct on the two fuel bounds together. If either fuel is zero, the corresponding strict inequality is impossible. With both positive, an input vertex unfolds directly to the same literal under either fuel. For a gate vertex, if its index corresponds to an actual gate, well-formedness lets us compare the two gate unfoldings argument by argument (`BoolCircuit.unfoldGate_congr`). Each argument has index below $v$ by the circuit's topological ordering, hence below both fuel bounds; the induction hypothesis identifies its two unfoldings. If there is no corresponding gate, both lookups use the same default constant gate, so the results agree directly.

**Key facts.** `BoolCircuit.unfoldGate_congr`.
