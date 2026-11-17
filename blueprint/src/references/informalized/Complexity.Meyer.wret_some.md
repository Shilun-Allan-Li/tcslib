<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineWalk.lean :: Complexity.Meyer.wret_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return Step at a Symbol

**Claim.** When the output tape contains a bit at its current head position, one tabulating-machine step keeps control in $\mathrm{wret}$, moves the output-tape head one cell left, and leaves the other lifted data and tape contents unchanged.

**Proof.** Rewrite the step from the lifted configuration as its transition applied to that configuration (`lcfg_step`). The auxiliary-tape read at the output head is exactly $\tau_O(z_O)$ (`aux_read2`), so the hypothesis that this value is a bit selects the nonblank branch of the $\mathrm{wret}$ transition. That branch makes no write, leaves the control state at $\mathrm{wret}$, and moves the output head by $-1$. The lifted-configuration update formula (`lcfg_apply_aux`) converts this action into the resulting tape contents and head positions; the tape is unchanged, and the output head is at $z_O-1$. Unfolding the lifted configuration and rewriting subtraction as addition of $-1$ yields the stated equality.

**Key facts.** `Complexity.Meyer.lcfg_step`, `Complexity.Meyer.aux_read2`, `Complexity.Meyer.lcfg_apply_aux`.
