<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Pad_seam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding Canonical Seam Configurations

**Claim.** Padding a canonical configuration with a word on tape zero, blank remaining tapes, and a specified output gives the corresponding canonical configuration on the padded number of tapes.

**Proof.** Compare the configuration fields. State, input-head position, and output are preserved by padding. For each tape index below $k$, padding retains the original tape and its head position, so the tape contents and head position match the canonical configuration. For an index at least $k$, the assumption $0<k$ ensures that the index is nonzero. Hence the state word assigns it the empty word; its tape is blank and its head is at zero on both sides. All fields agree, giving the claimed equality.
