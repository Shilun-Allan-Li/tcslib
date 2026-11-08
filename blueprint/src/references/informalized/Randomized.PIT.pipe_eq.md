<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.PIT.pipe_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pipeline test characterization

**Claim.** For all $n,m$ and bit strings $G_1,G_2,r$, the pipeline on the stated encoding returns true exactly when the two gate evaluations agree in every one of the $8(m+12)$ trials, using the context, raw block, and input points specified for each trial.

**Proof.** Let $z$ be the encoded input. Decoding its nested pairs recovers the unary encodings of $n$ and $m$, the two gate strings, and $r$. Hence the pipeline's trial counter consists of $8(m+12)$ true bits, while each trial consumes a block of $2(m+12)$ bits; the counter and block lengths therefore have the required values. The point-generation state starts with a counter of $m+4$ true bits, the unused tail of $r$, and no points. The iteration formula for `ptStep` shows that after the prescribed number of rounds it has accumulated exactly the blocks defining `pts n m r`, leaving the corresponding raw data in place. The pair projections then identify the pipeline's stored gate strings and point data. Applying the iteration formula for `trStep`, its final Boolean is the conjunction of the trial tests over all indices in the range. Each trial test compares the two modular evaluation bit strings through `beq`; by its definition, that Boolean is true precisely when their `bitsVal` values agree. Rewriting the conjunction as a universal quantifier over the range yields the stated characterization.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Randomized.PIT.iterate_ptStep`, `Randomized.PIT.iterate_trStep`, `Complexity.BinArith.forLoop_pairEncode`.
