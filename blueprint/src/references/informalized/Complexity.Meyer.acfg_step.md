<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.acfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step from an Auxiliary Configuration

**Claim.** The tabulating machine's step from an auxiliary configuration is the application of its tabulated transition to the scanned input symbol and the three symbols read from the auxiliary tapes, with the simulated work tapes blank.

**Proof.** The general one-step description for the tabulating machine (`tabTM_step`) says that its transition receives the current input symbol and the symbols under each work-tape head, with the resulting action applied to the configuration. In the auxiliary configuration, every simulated work tape is blank and each simulated head is at the origin, so every simulated read is blank. The three auxiliary reads are precisely the values of their respective tape contents at their specified head positions. Substituting these readings into the general step identity gives the claimed equality.

**Key facts.** `Complexity.Meyer.tabTM_step`.
