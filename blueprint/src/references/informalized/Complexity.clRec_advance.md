<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_advance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advancing a recorded source transition

**Claim.** The recorder can simulate one transition of $M$, advance exactly the movement counters selected by that transition, retain the record, clock budget, and logical time, and return to row-copy control within the stated step bound, with a tag valid for the new input-head position.

**Proof.** The proof begins with the tracking-round result (`clTrack_round`). It supplies a duration $\tau\le 2W+4$, a valid tag for the input-head position after one source step, and a run of the tracking machine that updates the source configuration to $M(c)$ and advances the counters according to the signed movements selected by the source transition. Its hypotheses include the given tag validity and the width bound on all counters. The recorder embeds this tracking machine into its larger collection of tapes. The one-step release fact (`clPlaced_release`) identifies the recorder’s transition out of the source-release control with the first tracking-machine step. The guarded simulation fact (`clPlaced_run`) then transfers the remaining tracking run to the recorder; the guard is verified at each intermediate tracking state from the intermediate-state information supplied by `clTrack_round`. A frame identity (`clRec_track_frame`) identifies the embedded tracking configuration with the recorder configuration while leaving its record, clock, and time tapes in place. Once tracking ends, the inactive-track and frame facts (`clRec_track_inactive` and `clRec_track_frame`) return the recorder to its ordinary control representation without changing those tapes or the updated source data. Counting the release step together with the tracking run gives $s=\tau+1\le 2W+5$. The final zero-movement control action preserves the input-head position, so the valid tag remains valid.

**Key facts.** `Complexity.clTrack_round`, `Complexity.clPlaced_release`, `Complexity.clPlaced_run`, `Complexity.clRec_track_frame`, `Complexity.clRec_track_inactive`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
