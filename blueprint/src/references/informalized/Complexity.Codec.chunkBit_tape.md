<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.chunkBit_tape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Slots in a Chunk

**Claim.** For a work-tape index $i$ and $r<3$, the bit at position $h_H+3i+r$ records whether the tape cell is nonblank when $r=0$, its Boolean symbol (defaulting to false when absent) when $r=1$, and whether the head is at that cell otherwise.

**Proof.** At the specified position, subtracting the state-slot width $h_H$ and dividing by three gives tape index $i$, while the remainder is $r$. Since $i$ is a valid work-tape index, the chunk encoding uses the corresponding tape-slot clause. Its three cases read, respectively, whether the tape symbol is present, the symbol with false as the default, and the head-position flag. The assumption $r<3$ ensures these are exactly the three possible remainder cases.
