<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.parallelCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding Scanned Tape Tracks

**Claim.** For each tape index $i<k$, decoding the bits read from its symbol-indexed encoded tracks recovers the possibly blank symbol under the original tape head.

**Proof.** Fix a tape index $i$. The encoded track corresponding to $(i,j)$ has the same head position as original tape $i$. Thus, as $j$ ranges over symbols of $A$, the bits read from these tracks are precisely the transverse code of the possibly blank symbol on tape $i$. Decoding this code returns that symbol by the decoding identity (Complexity.parallelDecode_code).

**Key facts.** `Complexity.parallelDecode_code`.
