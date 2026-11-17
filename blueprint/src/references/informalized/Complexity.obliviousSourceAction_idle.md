<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.obliviousSourceAction_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idle action in the halted state

**Claim.** When the selected state is absent, the selected action is stationary, makes no writes, emits no output, and has no successor state, regardless of the payload reads.

**Proof.** With absent state, the first branch of the selected-action definition applies. It returns the action with zero input movement, no write on every work tape, no output, and absent successor state. The payload reads do not enter this branch.
