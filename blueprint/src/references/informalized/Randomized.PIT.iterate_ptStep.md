<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.PIT.iterate_ptStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of point testing

**Claim.** After $i$ point-testing steps, the counter of $b$ ones is unchanged, the remaining input is $u$ with its first $ib$ bits removed, and the stored list is extended by the successive length-$b$ blocks beginning at positions $jb$ for $0\le j<i$.

**Proof.** Induct on $i$. At zero, the counter, input, and stored list are unchanged, as asserted. For the successor, substitute the induction hypothesis into one more point-testing step. The projections of a pair encoding recover its two components (`pairFstD_pairEncode` and `pairSndD_pairEncode`), so this step removes the next $b$ bits from the remaining input and appends the length-$b$ prefix of that remaining input to the stored list. Since the remaining input is $u$ with its first $ib$ bits removed, this appended block is the block of $u$ beginning at position $ib$. The list of block indices grows from $\{0,\ldots,i-1\}$ to include $i$, and $(i+1)b=ib+b$ gives the claimed remaining suffix.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.BinArith.encWords_append_singleton`.
