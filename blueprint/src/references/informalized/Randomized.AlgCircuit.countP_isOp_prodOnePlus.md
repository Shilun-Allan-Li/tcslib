<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuitExample.lean :: Randomized.AlgCircuit.countP_isOp_prodOnePlus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Operation count in the product circuit

**Claim.** For every natural number $n$, the constructed circuit for $\prod_{i=1}^{n}(1+X_i)$ contains exactly $2n$ arithmetic operation gates, counting addition, subtraction, and multiplication gates.

**Proof.** The circuit's gate list is the list generated for $n$ factors. The established count for that generated list is $2n$ (`countP_isOp_prodOnePlusGates`). Since the circuit uses precisely that list, the same count holds for its gates.

**Key facts.** `Randomized.AlgCircuit.countP_isOp_prodOnePlusGates`.
