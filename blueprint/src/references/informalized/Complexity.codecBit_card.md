<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecBit_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of Codec Bits

**Claim.** The number of codec-bit positions is $n+(n+2)+(|Q|+1)+3k(2s+1)+2$, where $Q$ is the machine's state set.

**Proof.** The codec-bit type is a disjoint union of positions for the input, input head, state, work tapes, and output summary. Their respective counts are $n$, $n+2$, $|\mathrm{Option}(Q)|=|Q|+1$, $k(2s+1)\cdot 3$, and $2$. Summing these counts and rearranging the product gives the stated formula.
