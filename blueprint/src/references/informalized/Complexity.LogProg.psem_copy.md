<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.psem_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Copying Preserves Semantics

**Claim.** If the destination register does not exceed the source register, and setting the destination equal to the source at the exit state has probabilistic semantics with acceptance probability $p$, then the equality-test state with the original valuation has the same semantics.

**Proof.** Let $k=v(src)-v(dst)$, a natural number by the assumed inequality. We induct on $k$. If $k=0$, then $v(dst)=v(src)$, so updating the destination to the source value leaves the valuation unchanged. The exit configuration therefore already has the required semantics, and the equality branch preserves it by the positive case of the equality-test principle (`PSem.jeq_pos`).

For the successor case, the destination and source values differ. Increase the destination by one to obtain a valuation $v'$. The source is unchanged because the indices are distinct; the new destination value is still at most the source value, and the register bound remains valid by the register-update bound (`register_update_le`). The exit configuration obtained by setting the destination to the source in $v'$ is exactly the exit configuration from the hypothesis, since the second update to the destination overwrites the first. The induction hypothesis thus gives the required semantics from the test state with valuation $v'$. The increment at the bump state leads to this configuration, so the increment principle (`PSem.inc`) gives semantics from the bump state with valuation $v$. Since the two tested registers are unequal there, the negative equality branch (`PSem.jeq_neg`) transfers those semantics back to the test state.

**Key facts.** `Complexity.LogProg.PSem.jeq_pos`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.PSem.inc`, `Complexity.LogProg.PSem.jeq_neg`.
