<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arMoveCfg_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the Move Sweep

**Claim.** One simulator step from the move-sweep configuration at counter zero yields the encoding of the configuration obtained by applying the original action.

**Proof.** At counter zero, the simulator is in the pending-move state with its sweep counter at zero. Its transition writes each pending work-tape symbol in encoded form at offset zero, leaves the work-tape heads stationary for this step, and returns to the ready state determined by the action's successor state. The encoded input position and output are those of the action-applied configuration already built into the move-sweep configuration. Comparing the state, input position, work-tape contents, head positions, and output shows that the resulting configuration is exactly the encoding of the action-applied configuration; the head-position equality is the direct arithmetic identity for offset zero.
