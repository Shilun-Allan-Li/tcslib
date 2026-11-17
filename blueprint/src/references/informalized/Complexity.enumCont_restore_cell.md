<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_restore_cell -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoring a Work Tape Cell

**Claim.** After applying an action, replacing tape $i$ at its original head position with the symbol that was there before the action restores tape $i$ exactly.

**Proof.** The action changes tape $i$ only, if at all, by updating its value at the original head position with the action's write value, using the old scanned symbol when no write is specified (`Turing.Action.apply_workTapes`). Updating that same position once more with the original scanned symbol therefore makes the two successive updates equivalent to a single update with that original value. Updating a function at a point with its existing value leaves the function unchanged, so the resulting tape is exactly the original tape.

**Key facts.** `Turing.Action.apply_workTapes`.
