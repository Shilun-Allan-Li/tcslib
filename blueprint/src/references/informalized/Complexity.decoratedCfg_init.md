<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean :: Complexity.decoratedCfg_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial decorated configuration

**Claim.** The decorated machine's initial configuration on an input is the decorated form of the original initial configuration, with the prescribed initial data state, blank extra tapes, and empty output.

**Proof.** Compare the configurations field by field. Their states pair the original initial state with the initial data state, and their input-head positions agree. For tape contents and head positions, split a tape index into an original-tape index or an extra-tape index: in the first case the decorated configuration uses the original initial tape, and in the second it uses the stipulated blank contents and the designated head's initial position. Both output words are empty. Hence all configuration fields agree.
