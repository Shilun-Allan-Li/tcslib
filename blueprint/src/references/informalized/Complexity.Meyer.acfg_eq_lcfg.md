<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.acfg_eq_lcfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Auxiliary Configurations

**Claim.** The auxiliary configuration with blank simulated tapes and heads at the origin equals the lifted initial configuration, when their state, input-head position, auxiliary contents and auxiliary head positions agree as specified.

**Proof.** Unfold both configuration constructions. Their state, input-head position, and output fields agree by their definitions. The lifted initial machine configuration has blank work tapes and all work heads at the origin, exactly matching the auxiliary configuration's simulated-tape fields. Its auxiliary tapes are the buffers for $x,t,a$, with heads at zero, as on the other side. Hence all configuration components agree.
