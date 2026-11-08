<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLoad_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding a Field-Loader Configuration

**Claim.** The placement of the two-tape configuration into the row loader’s slots yields exactly the row-loader configuration with the chosen field replaced and all other fields, the stream, and the cursor preserved.

**Proof.** Compare the two configurations component by component. Their control states and input-head positions agree by construction, as do their outputs. For the work tapes and head positions, split the row-loader slot index into a field slot or the stream slot. The placement selects the two simulated tapes in the swapped order used by the loader: the replacement word occupies field $i$, and the stream occupies the final slot. Every other field uses the row loader’s original tape contents, and all unselected heads are at zero. At field $i$, the tape function is exactly the pointwise update of `old` by `word`; hence the entire configurations agree.
