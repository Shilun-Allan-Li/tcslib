<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.pairDepth_parityPairs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of the Parity Literal Pairs

**Claim.** For every $n$, the pair depth of the list of opposite-polarity literal pairs at the $n$ variable indices is zero.

**Proof.** Expand the list of parity pairs and induct on the list produced by $\mathrm{List.finRange}(n)$. For the empty list, the fold defining pair depth has value zero. In the cons case, the head pair consists of two literals, each of depth zero. The leading-pair formula (`BoolCircuit.pairDepth_cons`) therefore makes the pair depth the maximum of zero and the tail's pair depth, which is zero by the induction hypothesis. Thus the full list has pair depth zero.

**Key facts.** `BoolCircuit.pairDepth_cons`.
