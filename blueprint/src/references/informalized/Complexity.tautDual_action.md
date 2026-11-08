<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_action -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Transducer Action

**Claim.** Applying the specified action to the specified configuration sets the new state, moves the input head according to the boundary-clamped movement rule, and appends the optional output bit when present.

**Proof.** The action and target configuration have the same state, input-head position, and output: these are respectively the chosen successor state, the moved position, and the old output followed by the optional symbol's list. There are no work tapes, so equality of those three fields suffices to identify the configurations by the zero-tape extensionality principle (`Cfg.ext_zero_tapes`).

**Key facts.** `Turing.Cfg.ext_zero_tapes`.
