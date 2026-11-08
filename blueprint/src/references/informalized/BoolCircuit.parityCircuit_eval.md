<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.parityCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity circuit evaluation

**Claim.** For every assignment $x:\mathrm{Fin}(n)\to\mathrm{Bool}$, the parity circuit evaluates to the iterated exclusive-or of the assigned bits, with initial value false.

**Proof.** Each pair in the parity-pair list consists of a variable's positive and negative literal. Under any assignment, these two literals have opposite values, so every pair satisfies the duality condition required by the XOR construction (`BoolCircuit.isDual_parityPairs`). The evaluation theorem for the fuelled XOR construction (`BoolCircuit.xorFuel_eval`) then identifies the first output's value with the iterated XOR of the list of pairs. For the parity-pair list, this iterated XOR is the fold over the finite range of indices of the assigned bits, starting from false (`BoolCircuit.xorAll_parityPairs`). Since the parity circuit is the first output of this fuelled construction on that list, the stated evaluation follows.

**Key facts.** `BoolCircuit.isDual_parityPairs`, `BoolCircuit.xorFuel_eval`, `BoolCircuit.xorAll_parityPairs`.
