<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.PIT.iterate_trStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of trial testing

**Claim.** After $i$ trial-testing steps, the query is unchanged, the remaining string has its first $i|q|$ bits removed, and the flag is its initial value conjoined with the trial-test outcomes on the first $i$ consecutive blocks of length $|q|$.

**Proof.** Induct on $i$. At zero, the remaining string and flag are unchanged, and the conjunction over no blocks is true. For the successor, substitute the induction hypothesis into one more trial-testing step. Pair projections recover the encoded query and remaining string (`pairFstD_pairEncode` and `pairSndD_pairEncode`); the step drops the next $|q|$ bits, tests the next block of that length, and conjoins the result with the current flag. The next block is the segment of the original string beginning at position $i|q|$. Thus the conjunction over the first $i$ blocks acquires exactly this additional factor, while the remaining suffix advances from dropping $i|q|$ bits to dropping $(i+1)|q|$ bits.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
