<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_track_action -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Tracked Machine's Source Step

**Claim.** When the source configuration has a present state, one step of the tracked machine from its completed tracked configuration is the intermediate stamping configuration for the source machine's one-step successor, with the same bounds.

**Proof.** Split on the source state. The absent-state case is excluded by the hypothesis. If the state is $q$, the tracked configuration is in the tracked machine's source-simulation state for $q$. Its input symbol is the same as the source configuration's, and its data-tape head symbols are exactly those of the source work tapes. The tracked transition therefore applies the source transition to those same observations. On the data tapes it performs the source writes and head movements; on the marker and origin tapes it makes the prescribed movements while preserving their contents in this phase. The resulting state records the source transition's successor, and the tape contents, head positions, input position, and output match the intermediate stamping configuration of the source successor.
