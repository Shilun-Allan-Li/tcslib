<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.rewind_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restart After Rewinding

**Claim.** If $j<r$, there is a position $p\le |x|$ such that words of length at most $p+2$ leave all work-tape head positions unchanged, and every word of length exactly $p+2$ takes the amplified machine from the rewind configuration to the restart at index $j+1$ and counter $c$.

**Proof.** Choose $p$ to be the input-head position after one attempted leftward move. This position is at most $|x|$ (`moveInputPos_neg_one_le`). The rewind action takes that leftward move and enters seek phase at index $j+1$, without changing the work-tape head positions. In seek phase, the machine moves left until reaching the left end, then starts the next run; the seek-run result says this takes exactly $p+1$ further choices, preserves work-tape head positions up to that bound, and yields the restart configuration (`rewind_run_pos`). Including the initial rewind choice gives the stated bound $p+2$ and exact total length. The first step’s action is the idle-action update (`idle_apply`), and the run on a nonempty word decomposes into its first choice followed by the rest (`Turing.NDTM.runWith_cons`).

**Key facts.** `Randomized.Amplify.moveInputPos_neg_one_le`, `Randomized.Amplify.rewind_run_pos`, `Randomized.Amplify.idle_apply`, `Turing.NDTM.runWith_cons`.
