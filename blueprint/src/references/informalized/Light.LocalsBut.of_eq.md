<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.LocalsBut.of_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Outside Refreshed Indices

**Claim.** If refreshing l at the indices in xs using the frame of l' produces a list with the same frame as l', then the frame of l' agrees with the frame of l at every index outside xs.

**Proof.** Fix an index y outside xs. The refresh-frame formula says that the refreshed list's frame at y is the original frame of l at y, since y is not among the refreshed indices (`Light.frame_refreshLocals`). By hypothesis, the refreshed list and l' have equal frames. Combining these equalities shows that the frame of l' at y equals the frame of l at y.

**Key facts.** `Light.frame_refreshLocals`.
