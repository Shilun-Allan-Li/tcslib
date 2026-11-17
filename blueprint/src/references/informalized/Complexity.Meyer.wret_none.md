<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineWalk.lean :: Complexity.Meyer.wret_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return Step at a Blank Cell

**Claim.** When the output tape is blank at its current head position, one tabulating-machine step changes control from $\mathrm{wret}$ to $\mathrm{wdec}$, advances the output-tape head by one, and leaves the other lifted data and tape contents unchanged.

**Proof.** Express the tabulating machine’s step from the lifted configuration as the transition applied to that configuration (`lcfg_step`). The transition in state $\mathrm{wret}$ reads the output auxiliary tape at its head; `aux_read2` identifies this read with $\tau_O(z_O)$. The assumed blank value selects the blank branch of the transition, which moves the output head one cell to the right and changes control to $\mathrm{wdec}$, with no write instruction on that tape. The lifted-configuration update formula (`lcfg_apply_aux`) then gives the resulting configuration: the output tape is unchanged, its head is at $z_O+1$, and all other displayed components retain their specified values. Unfolding the lifted configuration identifies this with the claimed result.

**Key facts.** `Complexity.Meyer.lcfg_step`, `Complexity.Meyer.aux_read2`, `Complexity.Meyer.lcfg_apply_aux`.
