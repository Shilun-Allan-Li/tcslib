<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.dec_under -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entering the Write-Decode State

**Claim.** If the $C$ buffer is blank at its head position, one simulator step from the decode state yields the write-decode state, retaining $P$, $c$, both buffers, and both head positions.

**Proof.** The lifted-configuration step formula expresses the simulator's move as its tabulated transition applied to the current lifted configuration (`lcfg_step`). In the decode state, the transition reads the $C$ buffer at auxiliary tape 1; that read is $\tau_C(z_C)$ (`aux_read1`), hence blank by hypothesis. The blank branch changes the control state to write-decode with saved simulated state $q$, and leaves every auxiliary tape untouched. Applying this action to the lifted configuration preserves the simulated input position, work tapes, both buffers, and their heads, as recorded by the auxiliary-action formula (`lcfg_apply_aux`). Rewriting these components in the notation of the lifted configuration gives the claimed equality.

**Key facts.** `Complexity.Meyer.lcfg_step`, `Complexity.Meyer.aux_read1`, `Complexity.Meyer.lcfg_apply_aux`.
