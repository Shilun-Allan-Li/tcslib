<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.ret_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return Transition at a Blank Cell

**Claim.** When the first auxiliary tape is blank at its head position in a return-state configuration, one tabulating-machine step changes the state to the corresponding decision state and advances that tape's head by one, leaving the other specified data unchanged.

**Proof.** The configuration-specific step formula (`Complexity.Meyer.lcfg_step`) expresses the tabulating machine's step as the transition selected by the current state and symbols under the heads. The return-state transition checks the first auxiliary tape; `Complexity.Meyer.aux_read1` identifies that symbol as $\tau_C(z_C)$, which is blank by hypothesis. In this branch the transition enters the corresponding decision state and moves the first auxiliary head one cell to the right, without writing on the auxiliary tapes or changing the output. Applying the action to the represented configuration has exactly this effect, by the auxiliary-action formula (`Complexity.Meyer.lcfg_apply_aux`): its tape contents are unchanged and its first auxiliary head position becomes $z_C+1$. This is the claimed represented configuration.

**Key facts.** `Complexity.Meyer.lcfg_step`, `Complexity.Meyer.aux_read1`, `Complexity.Meyer.lcfg_apply_aux`.
