<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.xorFuel_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth bound for XOR reduction

**Claim.** For a list of at most $k$ pairs of circuit trees, the maximum depth of the pair returned by the fuel-bounded XOR reduction is at most the pair depth of the original list plus $2\lceil\log_2 |ps|\rceil+2$.

**Proof.** Proceed by induction on the fuel and split according to whether the list is empty, a singleton, or has at least two entries. For the empty list, the reduction returns constant nodes of depth one, and the stated bound follows from the empty-list depth and logarithm conventions. For a singleton, the reduction returns that pair unchanged, whose maximum depth is bounded by the pair depth; the extra logarithmic and constant terms make the desired inequality immediate.

In the remaining case, write the list as $p,q$ followed by a tail. One pairing round replaces each consecutive pair by one XOR-step pair, leaving a final singleton unchanged if necessary. The length formula for this round gives $|\operatorname{xorPairUp}(ps)|=\lceil |ps|/2\rceil$, so the new list has length at most the reduced fuel. Apply the induction hypothesis to this shorter list. Its pair depth is at most the old pair depth plus two, by the pair-depth bound for one pairing round (`pairDepth_xorPairUp`). Also, since the old length is at least two, its base-two ceiling logarithm is exactly one more than the logarithm of the new length; this follows from the length formula and the ceiling-logarithm identity used in the proof. Combining these bounds gives the claimed inequality: the pairing round contributes at most two to pair depth, while the logarithmic term accounts for the halving at that round.

**Key facts.** `BoolCircuit.length_xorPairUp`, `BoolCircuit.pairDepth_xorPairUp`.
