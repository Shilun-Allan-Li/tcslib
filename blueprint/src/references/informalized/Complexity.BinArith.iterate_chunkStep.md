<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.iterate_chunkStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Chunk Processing

**Claim.** If $|w|=N|c|$ and either $c$ is nonempty or $N=0$, then applying the chunk-processing step $N$ times to the pair encoding of $c$ and the pair encoding of $w$ followed by the encoding of $L$ yields the pair encoding of $c$ and the pair encoding of the empty word followed by the encoding of $L$ with the $N$ consecutive chunks of $w$, each of length $|c|$, appended.

**Proof.** Proceed by induction on $N$. At $N=0$, no step is applied; the length condition forces $w$ to be empty, and the chunk list is empty, giving the stated form. For the successor case, the assumptions imply that $c$ has positive length. The length equation then implies that $w$ is nonempty. The chunk-step formula for a pair encoding shows that one step removes the first $|c|$ bits of $w$ and appends that prefix as one encoded word to the accumulator, leaving the rest of $w$ to process. The remaining word has length $N|c|$, so the induction hypothesis applies to it and the enlarged accumulator. Finally, the chunk-list definition identifies the resulting list of chunks with the first chunk followed by the chunks of the remaining word; the drop-and-take identities establish that these are exactly the consecutive length-$|c|$ chunks of the original $w$.

**Key facts.** `Complexity.BinArith.chunkStep_pairEncode`, `Complexity.BinArith.encWords_append_singleton`.
