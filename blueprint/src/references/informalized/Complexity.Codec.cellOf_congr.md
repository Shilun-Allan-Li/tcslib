<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.cellOf_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cell Encoding Depends on Core Data

**Claim.** If two configurations have the same state, input-head position, work-tape contents, work-tape head positions, and output summary, then their cell encodings agree at every index in the window.

**Proof.** Unpack equality of the configurations' core data together with their output summaries. The state, work-tape functions, and work-tape head positions therefore agree, and equality of output summaries gives equality of the summary used in the cell encoding. At any index, the encoding is determined by these data (with its head-and-summary slot present only at index $0$). Hence the two cell values agree at every index, and their cell functions are equal.
