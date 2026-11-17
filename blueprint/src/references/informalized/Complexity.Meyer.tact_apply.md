<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachine.lean :: Complexity.Meyer.tact_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Tabulation Action

**Claim.** Applying the action formed from the specified input, original-tape, and auxiliary-tape instructions to the given configuration produces the configuration with the chosen successor state, moved input head, prescribed tape updates and head movements, and appended optional output bit.

**Proof.** Unpack the action and configuration. Their state and output components agree directly: the successor state is the chosen one, and the output is the original word followed by the optional bit. For each work-tape index, split it into an original-tape index or an auxiliary-tape index. In either case, the action applies no change when no write is prescribed and updates the tape at its current head position when a write is prescribed; the corresponding head position increases by the specified movement. The input-head component is exactly the clamped movement prescribed by the action. Thus all five configuration components agree.
