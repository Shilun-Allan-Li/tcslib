<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.seek_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Returning from the seek phase

**Claim.** Starting in seek phase at input-head position $p\le |x|$, every choice word of length at most $p+1$ preserves all work-tape head positions, and every word of length exactly $p+1$ reaches the restarted configuration for run $j$ and counter $c$.

**Proof.** Induct on $p$. When $p=0$, the input head is already at the left boundary. The boundary-step rule (`Randomized.Amplify.step_seek_zero`) says that one step, for either choice bit, produces the restarted configuration. The empty word leaves the configuration unchanged, so its work-tape head positions are also unchanged; a word of length one has the required result.

For the successor case, write the position as $p+1$. One seek step moves the input head left by one and leaves every other component unchanged (`Randomized.Amplify.step_seek_pos`); the hypotheses ensure that the head is nonzero and within the input. Apply the induction hypothesis to the resulting configuration, now at position $p$. For a word of length at most $p+2$, its first bit performs this leftward step and its remaining suffix has length at most $p+1$, so the induction hypothesis gives preservation of the work-tape head positions. For a word of length exactly $p+2$, the suffix has length exactly $p+1$ and the induction hypothesis says it reaches the restarted configuration. Since restart changes only the state and input-head position, the unchanged work-tape head positions are exactly those required.

**Key facts.** `Randomized.Amplify.step_seek_zero`, `Randomized.Amplify.step_seek_pos`, `Turing.NDTM.runWith_cons`.
