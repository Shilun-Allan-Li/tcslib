<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.acceptCfg_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility of Actions with the Configuration Map

**Claim.** Applying the transformed action that records the last output bit to the corresponding configuration gives the same configuration as first applying the original action and then forming its corresponding configuration.

**Proof.** The transformed action preserves the input-head movement and all work-tape actions, while its output is empty and its state records the old state together with the updated output bit. The only component requiring an identity is the recorded bit: the last bit of the new output, with `false` as the default, equals the action's output bit when present and otherwise the previous last bit (`hlast`). The two sides therefore have the same state; their input positions, work tapes, and work-tape head positions agree directly from the definitions. Both corresponding configurations have empty output. Equality of all configuration fields proves the claim.
