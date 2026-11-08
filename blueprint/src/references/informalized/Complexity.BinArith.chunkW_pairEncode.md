<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.chunkW_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chunking a paired bit string

**Claim.** If $|w|=N|c|$ and either $|c|>0$ or $N=0$, then chunking the encoding of $c$ paired with $w$ produces the encoding of the $N$ consecutive chunks of $w$, each of length $|c|$.

**Proof.** The proof first notes that $N\leq |w|$: when $|c|>0$, this follows from $|w|=N|c|$, and when $N=0$ it is immediate. The chunk-step iteration theorem (`iterate_chunkStep`) then says that after $N$ steps, the state is the encoding of $c$ paired with the empty remainder and with the accumulated encodings of the chunks listed by `chunkList`. The outer loop on a paired encoding removes one position from its first component per iteration and applies its function to the second component (`forLoop_pairEncode`); thus the loop runs the chunk step the required number of times while preserving the encoded state structure. Since the first component is then empty, one further chunk step fixes the state. Reassembling the decoded output therefore gives precisely the encodings of the listed chunks.

**Key facts.** `Complexity.BinArith.iterate_chunkStep`, `Complexity.BinArith.forLoop_pairEncode`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
