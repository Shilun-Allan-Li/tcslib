<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.mv_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded register transfer

**Claim.** Under the stated register bounds and the bound on the sum of the source and destination values, the move operation transfers the source value to the destination, clears the source, and keeps every configuration before termination within the guard.

**Proof.** The move routine has three phases: test whether the source is zero, decrement it if it is nonzero, and increment the destination before returning to the test. Thus it repeats exactly as many times as the source’s initial value, then exits with the source cleared and the destination increased by that value. The source and destination are distinct (`mv_ne`), so these updates do not interfere. The bound on every initial register follows from the state bound (`St.Bd.toV`). During the loop, the source only decreases and the destination only increases; their sum stays constant, so the assumed bound on that sum keeps both registers at most $B$. Every other register remains unchanged. The routine’s three instruction transitions are precisely the hypotheses of the general move-loop result (`move_run`), which yields the required guarded reachability and final state.

**Key facts.** `Complexity.LogProg.SavitchARM.mv_ne`, `Complexity.LogProg.SavitchARM.St.Bd.toV`, `Complexity.LogProg.move_run`.
