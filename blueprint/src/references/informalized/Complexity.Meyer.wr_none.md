<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.wr_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No-Write Tape Update

**Claim.** If no symbol is prescribed for writing, applying the write operation leaves the tape contents unchanged.

**Proof.** By definition, the write operation returns the original tape when its write instruction is absent. Hence the resulting tape function equals $\tau$ by unfolding the definition.
