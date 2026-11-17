<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.pcfg_fB_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False Branch from the Second Field State

**Claim.** When the input symbol at position $p-1$ is false, one step from state $fB$ advances the input head to $p+1$ and enters $cpy$ if $f$ is true, or $fA$ with flag true if $f$ is false, preserving the bit vector and auxiliary words.

**Proof.** First, the one-step configuration formula for a buffered configuration (`pcfg_step`) identifies the transition rule's input symbol as $y[p-1]?$. The hypothesis makes this symbol false, so the false-input branch of the $fB$ transition applies: it moves the input head right, leaves the auxiliary tapes idle, and selects $cpy$ or $fA$ with flag true according to $f$. The action-on-configuration formula for an idle auxiliary action (`tact_idle_apply`) then shows that the auxiliary tapes, their head positions, and the output are unchanged. Finally, moving right from the clipped position for $p$ gives the clipped position for $p+1$ (`moveInputPos_fpos`); the bounds on $p$ ensure this is the desired position. Unfolding the buffered configuration yields the stated equality.

**Key facts.** `Complexity.Meyer.pcfg_step`, `Complexity.Meyer.tact_idle_apply`, `Complexity.Meyer.moveInputPos_fpos`.
