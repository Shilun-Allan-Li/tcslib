<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecObserve_step_normalize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step Invariance Under Output Normalization

**Claim.** Replacing a configuration’s output by the word encoding its output summary does not change the observation of its one-step successor.

**Proof.** The output affects the core sum only through its output summary, while the transition’s other successor data are unchanged by replacing an output with another word having the same summary. The summary word represents exactly the original summary (`codecSummaryWord_summary`). Consequently, the original configuration and the one with normalized output have equal core sums, and the step-preservation theorem for core sums (`Turing.NDTM.coreSum_stepWith`) gives equal core sums for their one-step successors. Since equal core sums determine equal observations (`codecObserve_congr`), the two successor observations agree.

**Key facts.** `Complexity.codecObserve_congr`, `Turing.NDTM.coreSum_stepWith`, `Complexity.codecSummaryWord_summary`.
