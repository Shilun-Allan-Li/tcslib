<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clTrack_dispatch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatch to the anchor configuration

**Claim.** One step from the specified starting configuration of the tracking machine yields the anchor configuration with the prescribed source state, tag, counters, heads, and output.

**Proof.** In the starting state, the tracking machine has its bank phase active with every bank state at zero. Its transition therefore takes the branch that dispatches to the reference configuration, leaving the administrative tapes and their heads unchanged and preserving the source data and output. The resulting control action updates the state and input-head position as prescribed; a zero input movement leaves that position fixed (`Turing.moveInputPos_zero`). The control-action update rule (`Turing.FinTM.controlAction_apply`) gives these configuration fields, and unfolding the definitions identifies the result with the anchor configuration.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
