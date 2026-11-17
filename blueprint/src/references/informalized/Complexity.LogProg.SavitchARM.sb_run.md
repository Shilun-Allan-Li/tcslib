<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.sb_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stack Pop Routine Run

**Claim.** For any bounded register state, the phase-zero subtraction routine reaches the move routine for recovering the popped endpoint, clears $Q$, and replaces $SE$ by the truncated difference $SE-Q$, with the other registers unchanged and the guard maintained before the endpoint.

**Proof.** The subtraction loop begins by testing whether $Q$ is zero. While it is nonzero, it decrements $Q$ and decrements $SE$ once, then repeats. Thus it performs exactly the original value of $Q$ paired decrements of $SE$, with natural-number subtraction truncated at zero. The loop exits with $Q=0$ and $SE$ equal to the original $SE-Q$, leaving every other register unchanged. The general subtraction-loop reachability result also supplies the guard at every configuration before the final one. Its distinct-register hypothesis holds because $Q$ and $SE$ are different registers; the state bound follows from the assumed componentwise bound on the eighteen registers.

**Key facts.** `Complexity.LogProg.SavitchARM.St.Bd.toV`, `Complexity.LogProg.sub_run`.
