<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.xorAll_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Xor Over a List With a Leading Pair

**Claim.** For a list of circuit pairs with leading pair $p$, the accumulated exclusive-or of the first circuit in each pair is the exclusive-or of the first circuit in $p$ with the corresponding accumulation over the remaining list.

**Proof.** The accumulation is defined by folding from the right, using exclusive-or with the first circuit's value at each pair and false as the initial value. Unfolding this definition at the leading pair gives its first-circuit value xor the accumulation over the remaining list, as claimed.
