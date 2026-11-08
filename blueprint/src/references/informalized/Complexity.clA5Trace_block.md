<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Trace_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blocks of the Trace Assignment

**Claim.** For a finite binary machine $M$, a binary code for its optional states, an input word $y$, and time $t$, the block of trace-assignment variables at time $t$ equals the binary encoding of the machine's snapshot at that time on input $y$.

**Proof.** Fix a coordinate $i$ of the block, and write $B$ for the block width. The variable index assigned to this coordinate is $|y|+tB+i$. It is not among the initial input positions, since it is at least $|y|$. After subtracting $|y|$, division by the positive width $B$ gives quotient $t$ and remainder $i$: here $i<B$ because it is a block coordinate. The trace assignment therefore selects snapshot $t$ and coordinate $i$ from its encoded block. Since this holds at every coordinate, the blocks are equal. Positivity of the width is supplied by `clA5Width_pos`.

**Key facts.** `Complexity.clA5Width_pos`.
