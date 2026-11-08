<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.RW_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Contents After One Step

**Claim.** After one machine step, the symbol at offset $d$ on work tape $h$ is given by the work-tape update rule applied to the current state and reads, using the prior tape contents as the default.

**Proof.** Split first into halted and active configurations. A halted configuration remains unchanged, so its tape contents are the previous contents at offset $d$, exactly the halted branch of the update rule (`Turing.MultiTapeTM.step_of_halt`).

For an active configuration in state $q$, the machine step applies the transition determined by the current reads (`Complexity.Meyer.step_eq`). Fix tape $h$, and let the transition's work-tape instruction be a write option $w$ together with movement $m$. If $w$ is absent, the tape function is unchanged. The new head is displaced by $m$, so the cell at offset $d$ from that head is the old cell at offset $d+m$ from the old head. The update rule tests exactly whether $d+m=0$: in that case it returns the symbol read at the old head (which is the default for an absent write); otherwise it returns the old contents at offset $d+m$.

If $w$ specifies a symbol, the transition updates the old tape function at the old head location to that symbol. Thus when $d+m=0$, the queried cell is exactly the updated location and contains the written symbol. When $d+m\ne0$, the queried cell is a different location, so it retains its old contents at offset $d+m$. These are precisely the two branches of the work-tape update rule.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Complexity.Meyer.step_eq`.
