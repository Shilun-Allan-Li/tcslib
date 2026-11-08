<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationCodec_step_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Step Is Determined by the Configuration Code

**Claim.** For configurations on the same input satisfying the window condition, equality of their configuration codes implies that their one-step successors have equal states, input-head positions, work-tape contents, work-tape head positions, and output summaries.

**Proof.** By injectivity of the configuration encoding on configurations satisfying the window condition, equality of the codes implies equality of the configurations' core data and output summaries (`configurationCodec_eq_iff`). The one-step transition preserves equality of this summarized data: equal summaries determine the same successor summary under the machine step (`Turing.NDTM.coreSum_stepWith`). Applying this fact to the two configurations proves the result.

**Key facts.** `Complexity.configurationCodec_eq_iff`, `Turing.NDTM.coreSum_stepWith`.
