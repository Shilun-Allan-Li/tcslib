<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.rewind_run_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Position-Dependent Rewind Restart

**Claim.** For $j<r$, let $q$ be the input-head position after one attempted move left from $C$. Words of length at most $q+2$ leave the work-tape head positions unchanged, and every word of length exactly $q+2$ yields the restart of $C$ at index $j+1$ and counter $c$.

**Proof.** For either first choice, the rewind transition takes its nonfinal-index branch: it moves the input head one step left and enters seek phase at index $j+1$, leaving the work tapes and their head positions alone. The idle-action description specifies this update (`idle_apply`); the transition from a configuration in the stated phase is identified by `step_of_state`. Apply the seek-run result at the resulting input position $q$. It gives preservation of work-tape head positions for at most $q+1$ further choices and the restart after exactly $q+1$ choices (`seek_run`). Including the initial rewind choice yields the bound $q+2$ and the asserted restart length. Decomposing any nonempty choice word into its first bit and suffix makes both conclusions follow from that seek-run analysis (`Turing.NDTM.runWith_cons`).

**Key facts.** `Randomized.Amplify.step_of_state`, `Randomized.Amplify.idle_apply`, `Randomized.Amplify.seek_run`, `Turing.NDTM.runWith_cons`.
