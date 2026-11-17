<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Configuration.lean :: Turing.Cfg.ext_zero_tapes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extensionality with No Work Tapes

**Claim.** For two configurations with no work tapes, equality of their optional states, input-head positions, and output words implies equality of the configurations.

**Proof.** Configurations are equal once their state, input-head position, work-tape contents, work-tape head positions, and output agree. The first, second, and last components agree by hypothesis. Since there are no work tapes, there are no indices at which either of the two work-tape functions can differ; both functions agree pointwise vacuously. Thus every component agrees, so the configurations are equal.
