<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.pairDepth_xorPairUp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Bound for Pairwise XOR Construction

**Claim.** For every finite list of circuit pairs, the pairwise XOR construction has pair depth at most two plus the original list's pair depth.

**Proof.** Proceed by the list cases used in the recursive definition of the construction. For the empty list, both pair depths are zero. For a singleton, the construction leaves the pair unchanged, so its depth is bounded by two plus its original depth. For a list $p::q::ps$, the output begins with the XOR construction of $p$ and $q$, followed by the recursive construction on $ps$. The leading-pair formula expresses its depth as the maximum of the new head depth and the recursive tail depth (`BoolCircuit.pairDepth_cons`). The XOR-pair depth bound controls the head by two plus the maximum of the depths of $p$ and $q$ (`BoolCircuit.pairDepth_xorNode`); the induction hypothesis controls the tail by two plus the depth of $ps$. Together with the same leading-pair formula for the original list, these bounds imply the claimed overall estimate.

**Key facts.** `BoolCircuit.pairDepth_cons`, `BoolCircuit.pairDepth_xorNode`.
