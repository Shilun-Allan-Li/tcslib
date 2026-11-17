<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.mulL_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded multiplication loop

**Claim.** Starting with counter $c$, zero scratch register, and $T+cP\le B$, the multiplication loop reaches its finish label with counter zero and accumulator $T+cP$, while maintaining the register bound and validity guard before termination.

**Proof.** Induct on $c$. If $c=0$, the loop's zero test branches directly to the finish label, leaving the registers unchanged; the desired accumulator is $T$, and reflexivity followed by the initial-step rule gives the guarded run. For $c+1$, the loop decrements the counter to $c$ and copies $P$ into the accumulator $T$ using `cp_run` (the bounded copy-loop result). The intermediate state remains bounded, and its accumulator plus the remaining counter's contribution is at most $B$, because $(c+1)P=P+cP$. Apply the induction hypothesis to this state, obtaining accumulator $T+P+cP=T+(c+1)P$ and zero counter. The loop then clears $P$ to reach the finish label. Concatenating these segments with `AReach.trans`, and accounting for the one-step transitions with `step_of` and the state-identification rule `reach_of_eq`, proves the result and preserves the guard.

**Key facts.** `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.SavitchARM.step_of`, `Complexity.LogProg.SavitchARM.cp_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.reach_of_eq`.
