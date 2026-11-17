<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.LocalsBut.update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a Local Variable

**Claim.** If loc agrees with the frame of l outside xs, then updating loc at x to z agrees outside xs with the frame of the list obtained by setting l's entry at x to z.

**Proof.** Fix y outside xs. Updating the list changes its frame at y to z if y=x and otherwise leaves it equal to the old frame (`Light.frame_setLocal`). The function update has the same behavior: its value at y is z if y=x and otherwise is loc(y). Thus the updated function's value at y equals the updated list's frame there, using the assumed agreement between loc and the old frame at y.

**Key facts.** `Light.frame_setLocal`.
