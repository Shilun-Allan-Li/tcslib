<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.rewind_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running Through the Rewind Phase

**Claim.** For a choice word of length $m+2$, the host run starting in phase $	ext{rew}$ with yard head at $m$ ends in phase $	ext{run}$ with $A$ in its initial state and no captured output. Its yard head is at zero, its input head is the result of $m+1$ clamped left moves followed by one right move, and the other tape data and output are unchanged.

**Proof.** Write the choice word as its first bit followed by a suffix of length $m+1$. The first bit performs the initial rewind step (`rew_step`), taking the host to phase $	ext{rew}$'s successor, $	ext{rew2}$, with the input head moved left and the yard head at $m-1$. Split the suffix into its first $m$ bits and its final bit. The first $m$ bits rewind across the marked yard cells: `rew2_marks` says that they leave the host in phase $	ext{rew2}$, move the input head left by $m$ further clamped steps, and bring the yard head to $-1$. The final bit then takes the empty-yard branch of the rewind transition, entering phase $	ext{run}$ with $A$'s initial state and no captured output, moving the input head right and the yard head to zero (`rew2_turn`). The run concatenation and one-step identities (`runWith_append`, `runWith_cons`, and `runWith_nil`) assemble these successive segments; the given length equation ensures the split has exactly the required sizes. Each step leaves the two machine tape blocks and output untouched, so they retain their original data throughout.

**Key facts.** `Turing.ClockHost.rew_step`, `Turing.NDTM.runWith_append`, `Turing.ClockHost.rew2_marks`, `Turing.NDTM.runWith_cons`, `Turing.ClockHost.rew2_turn`, `Turing.NDTM.runWith_nil`.
