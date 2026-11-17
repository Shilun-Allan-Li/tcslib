<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.xorAll_xorPairUp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing Preserves Accumulated Xor

**Claim.** If each pair consists of a circuit and its Boolean negation under $x$, replacing successive pairs by the paired circuit construction preserves the accumulated exclusive-or of the first circuits.

**Proof.** Use induction on the list of pairs. The empty list and a singleton are unchanged by the pairing operation, so their accumulations agree. For a list beginning with $p,q$ and followed by a tail, the duality hypotheses restrict to the tail, so induction gives equality of the tail accumulations. The accumulation rule for a leading pair (`BoolCircuit.xorAll_cons`) expresses each side as the leading first-circuit value xor its tail. The paired construction's first circuit evaluates to the xor of the first-circuit values of $p$ and $q$ when both pairs are dual (`BoolCircuit.xorNode_eval`). Substituting this and the tail equality reduces the claim to associativity of Boolean xor: grouping the first two values before the tail gives the same result as accumulating them successively.

**Key facts.** `BoolCircuit.xorAll_cons`, `BoolCircuit.xorNode_eval`.
