<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.swapKinds_swapKinds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involution of Gate-Kind Swapping

**Claim.** For every bit string $w$, applying twice the bit-string transformation that swaps AND and OR gate kinds returns $w$.

**Proof.** The transformation is the finite-state map $T$ started in its initial state. The auxiliary involution identity says that applying $T$ twice to any bit string, with the same starting state, returns that string (`T_T`). Taking the initial state and the given input $w$ yields the claimed equality.

**Key facts.** `BoolCircuit.CktSatReduction.T_T`.
