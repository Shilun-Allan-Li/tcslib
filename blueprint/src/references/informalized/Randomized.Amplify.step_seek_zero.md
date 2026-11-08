<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.step_seek_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restart from the left boundary

**Claim.** At input-head position zero in seek phase for run $j$ and counter $c$, one amplified step sets the state to the start of run $j$ with counter $c$ and moves the input head to position one, retaining the other configuration data.

**Proof.** At position zero the scanned input symbol is absent. The phase-specific step identity (`Randomized.Amplify.step_of_state`) therefore reduces the step to the seek transition on an absent symbol. This transition is idle on work tapes and output, sets the state to run $j$ from the initial state with empty output summary and counter $c$, and moves the input head right. The idle-action identity (`Randomized.Amplify.idle_apply`) makes these component updates explicit; at position zero the rightward move gives position one. These are precisely the components of the stated restart configuration.

**Key facts.** `Randomized.Amplify.step_of_state`, `Randomized.Amplify.idle_apply`.
