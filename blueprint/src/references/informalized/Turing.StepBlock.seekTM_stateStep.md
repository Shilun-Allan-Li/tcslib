<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.seekTM_stateStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seek State Transition

**Claim.** When the seek machine is in its state control with rank `rank`, one step advances the summary head and issues a request carrying the maximum rank remainder and a false flag if the scanned bit is true. If the bit is false, it leaves the configuration’s tapes and head positions unchanged and enters done when the rank is zero, or requests the preceding rank with a true flag otherwise.

**Proof.** The hypothesis identifies the symbol under the summary head with `b`. Unfolding one step of the phase-hosted seek machine exposes its state-control transition: when `b` is true, that transition is a tape action on the summary tape, moving its head one cell to the right, and its successor control is a request with the original rank, remainder one below the number of possible ranks, and flag false. When `b` is false, the transition is an input-move action with zero movement and no tape writes; its successor control is done if the rank is zero, and otherwise a request with remainder `rank - 1` and flag true. The configuration extensionality check confirms that these control changes and, in the true case, the single summary-head advance are exactly the configurations stated.
