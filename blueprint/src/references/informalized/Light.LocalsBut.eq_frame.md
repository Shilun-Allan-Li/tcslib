<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.LocalsBut.eq_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frame After Refreshing Locals

**Claim.** If loc agrees with the frame of l outside xs, then loc is the frame of the list obtained by refreshing l at the indices in xs using loc.

**Proof.** Compare the two functions at an arbitrary index y. The frame of the refreshed list is given by the refresh-frame formula: it is loc(y) when y belongs to xs, and otherwise it is the original frame of l at y (`Light.frame_refreshLocals`). In the first case the values agree by definition; in the second they agree by the assumed agreement outside xs. Thus the functions agree at every index.

**Key facts.** `Light.frame_refreshLocals`.
