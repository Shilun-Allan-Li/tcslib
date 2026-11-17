<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.RW_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Work-Tape Contents

**Claim.** In the initial configuration, every work-tape cell, including the cell at any integer offset from its head, contains no symbol.

**Proof.** The initial configuration assigns the empty tape function to every work tape and places each work-tape head at position zero. Hence the tape contents at the head position plus any offset are absent, as asserted.
