<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.NDTM.coreSum_stepWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Core data and output summary after one choice

**Claim.** If two configurations have the same core data and output summary, then after one step under the same Boolean choice they again have the same core data and output summary.

**Proof.** Equality of the combined core-and-summary pair gives separately equal core data and equal output summaries, by projecting to the first and second components. Regard the step under the fixed choice as a step of the corresponding deterministic machine with that choice fixed (Turing.NDTM.stepWith_eq_fixChoice_step). The core-step theorem for this machine preserves equality of the state, input position, tape contents and head positions (Turing.MultiTapeTM.ConfigCount.core_step). For the output component, a step appends the same emitted symbol to each output word: the emitted symbol agrees because it depends only on the equal core data (Turing.NDTM.outputSymbol_congr), and the output of a step is the prior output followed by that emitted symbol (Turing.MultiTapeTM.step_output). Equal prior summaries remain equal after appending the same emitted word (Turing.outSummary_append_congr). Combining the equal new core data and equal new summaries proves the claim.

**Key facts.** `Turing.NDTM.stepWith_eq_fixChoice_step`, `Turing.MultiTapeTM.ConfigCount.core_step`, `Turing.MultiTapeTM.step_output`, `Turing.NDTM.outputSymbol_congr`, `Turing.outSummary_append_congr`.
