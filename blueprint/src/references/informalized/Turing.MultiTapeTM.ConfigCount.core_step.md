<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.ConfigCount.core_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step evolution determined by the core

**Claim.** If two configurations have equal cores, then after one step their cores are equal.

**Proof.** Equality of cores gives equality of the states, input-head positions, tape contents, and work-head positions. Therefore the input symbols currently read agree, since they are determined by the input-head position, and the tuples of symbols read from the work tapes agree, since both the tape contents and head positions agree. If the common state is halting, both configurations remain unchanged and their cores remain equal. Otherwise, the machine receives the same state and read symbols in both configurations, so its deterministic transition supplies the same action. Applying this action preserves equality of the state, input position, tape contents, and work-head positions: each update uses the same action and the same positions. The output component is not part of the core and need not be compared.
