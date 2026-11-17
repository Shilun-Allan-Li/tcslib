<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.xorCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the XOR circuit

**Claim.** The specified Boolean circuit for exclusive-or evaluates to true exactly when the two input values differ.

**Proof.** Unfold the circuit evaluation and the definitions of its gates. The resulting expression is the usual Boolean exclusive-or of $x(0)$ and $x(1)$: it is true in the two cases $(x(0),x(1))=(\mathrm{false},\mathrm{true})$ and $(\mathrm{true},\mathrm{false})$, and false when the inputs agree. Thus the circuit evaluates to true exactly when $x(0)\ne x(1)$.
