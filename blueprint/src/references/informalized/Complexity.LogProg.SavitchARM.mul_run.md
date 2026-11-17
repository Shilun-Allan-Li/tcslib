<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.mul_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded multiplication routine

**Claim.** If the counter, accumulator, and scratch register start at zero, the registers are bounded by $B$, and the required product is at most $B$, then the multiplication routine reaches its exit label with the power register equal to that product, with the guard maintained before termination.

**Proof.** Let $F$ be the chosen multiplier: $P$ when the flag is true and $a$ otherwise. The initial register bound gives $F\le B$. First, `cp_run` copies $F$ into the counter. Then `mulL_run` executes the multiplication loop with counter $F$: since the accumulator and scratch register start at zero, it leaves counter zero and puts $FP$ in the accumulator. The assumed product bound ensures the intermediate and final register bounds. The routine clears the power register and transfers the accumulator back into it via `mv_run` (the bounded move-loop result). This yields the requested product in the power register. The runs concatenate using `AReach.trans`; the explicit one-step transition is covered by `step_of`, and `reach_of_eq` identifies the final register state with the stated update.

**Key facts.** `Complexity.LogProg.SavitchARM.cp_run`, `Complexity.LogProg.SavitchARM.mulL_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.SavitchARM.step_of`, `Complexity.LogProg.SavitchARM.mv_run`, `Complexity.LogProg.reach_of_eq`.
