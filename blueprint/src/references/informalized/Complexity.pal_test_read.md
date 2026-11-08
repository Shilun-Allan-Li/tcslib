<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.pal_test_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Reversed Bit

**Claim.** For a binary word $x$ and $i<|x|$, the work tape in the specified test configuration contains at its head the bit of the reversal of $x$ at position $i$.

**Proof.** Write $n=|x|$. The work head is at integer position $n-1-i$, which is the natural number $n-1-i$ viewed as an integer. This position is nonnegative and less than $n$, so the tape definition reads the entry of $x$ at that natural index. The list reversal indexing formula identifies this entry with the bit of $x.reverse$ at position $i$, as required.
