<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.T_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transduction of a leading bit

**Claim.** For every state $q$, bit $b$, and finite bit string $w$, processing $bw$ from state $q$ outputs the bit obtained by swapping $b$ according to $q$, followed by the result of processing $w$ from the next state determined by $q$ and $b$.

**Proof.** This is the recursive definition of the transducer on a nonempty input: it outputs the swapped version of the first bit, then continues on the remaining string from the state reached upon reading that bit.
