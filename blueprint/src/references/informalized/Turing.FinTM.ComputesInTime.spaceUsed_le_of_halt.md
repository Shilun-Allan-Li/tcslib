<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.FinTM.ComputesInTime.spaceUsed_le_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound Persists After Halting

**Claim.** If $M$ computes $w$ from $x$ within $t$ steps and has used at most $s$ work-tape cells through step $t$, then its space usage through every later or earlier time $t'$ is at most $s$.

**Proof.** The computation-time hypothesis says that the run is halted at time $t$ (`computesInTime_iff`). For each tape, any position visited by time $t'$ either occurs at some time $u\le t$, and so was visited through $t$, or occurs at $u>t$. In the latter case, write $u=t+(u-t)$. The configuration stays fixed after halting, so the head position at $u$ equals its position at $t$ (`runFrom_add` and `runFrom_of_halt`). Thus the visited-position set through $t'$ is contained in the set through $t$. Taking cardinalities tape by tape and summing shows that total space through $t'$ is at most the total through $t$, which is at most $s$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
