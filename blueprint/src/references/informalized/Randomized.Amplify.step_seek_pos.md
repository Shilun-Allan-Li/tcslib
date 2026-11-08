<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.step_seek_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input head moves left during seeking

**Claim.** In the seek phase, when the input-head position is nonzero and at most $|x|$, either choice bit changes only that position, decreasing it by one.

**Proof.** The position bounds place the head on an input symbol, so its scanned symbol is present. The phase-specific step identity (`Randomized.Amplify.step_of_state`) reduces the amplified step to its prescribed transition. In the seek phase with a present symbol, that transition is idle on all work tapes and output and sets the input-head movement to the left (`Randomized.Amplify.idle_apply`). Consequently the state, tapes, tape-head positions, and output are unchanged. Since the input position is nonzero, moving left sends it to the position one less (`Turing.moveInputPos_neg_of_ne_left`).

**Key facts.** `Randomized.Amplify.step_of_state`, `Randomized.Amplify.idle_apply`, `Turing.moveInputPos_neg_of_ne_left`.
