<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arSpacePhase_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulator phase along a run

**Claim.** At every simulator time $t$, there is a source time $s\le t$ such that the simulator is either the encoding of the source configuration at time $s$, or is in a reading, writing, or moving phase associated with that source configuration and a nonhalting source state.

**Proof.** Induct on the simulator time. At time zero, the simulator is exactly the encoding of the initial source configuration, so take $s=0$. For the successor time, apply the one-step phase analysis (`arSpacePhase_step`) to the phase supplied by induction. If the next simulator configuration remains associated with the same source configuration, keep the same source time $s$. If it is associated instead with the next source configuration, increase the source time to $s+1$. In both cases the chosen source time is no greater than the new simulator time, and the successor-run identity (`runFrom_succ_eq_step'`) identifies these one-step transitions with the configurations at the claimed times. This proves the assertion for every time.

**Key facts.** `Turing.FinTM.arSpacePhase_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
