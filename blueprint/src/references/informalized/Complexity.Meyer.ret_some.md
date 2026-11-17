<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.ret_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return Transition at a Nonblank Cell

**Claim.** When the first auxiliary tape contains a bit at its head position in a return-state configuration, one tabulating-machine step stays in the same return state and moves that tape's head one cell to the left, leaving the other specified data unchanged.

**Proof.** The configuration-specific step formula (`Complexity.Meyer.lcfg_step`) reduces the step to the transition selected from the symbols under the heads. By `Complexity.Meyer.aux_read1`, the first auxiliary symbol is $\tau_C(z_C)$, and the hypothesis says it is a bit rather than blank. Thus the return-state transition takes its nonblank branch: it remains in the same return state, makes no tape writes, and moves the first auxiliary head left by one. The auxiliary-action formula (`Complexity.Meyer.lcfg_apply_aux`) translates this action back to the represented configuration, retaining the tape contents and other specified data and changing the head position to $z_C-1$.

**Key facts.** `Complexity.Meyer.lcfg_step`, `Complexity.Meyer.aux_read1`, `Complexity.Meyer.lcfg_apply_aux`.
