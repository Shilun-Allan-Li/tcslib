<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.pairFanin_parityPairs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity pairs have zero fanin

**Claim.** For every natural number $n$, the list of pairs of opposite-polarity literals at the indices from $0$ to $n-1$ has pair fanin $0$.

**Proof.** The list of parity pairs is obtained by mapping each index in the finite range to a pair of literals. Induct on that finite-range list. The empty list has pair fanin $0$ by the fold definition. In the cons case, the head consists of two literals, each of fanin $0$; the pair fanin recursion therefore takes the maximum of $0$ and the tail's pair fanin, which is $0$ by induction.

**Key facts.** `BoolCircuit.pairFanin_cons`.
