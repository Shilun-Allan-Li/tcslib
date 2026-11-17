<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_factor_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factor Multiplication Run

**Claim.** Starting with register $11$ zero, the machine reaches the length-bound state for the inner factor or the tail-test state for the outer factor, multiplying register $7$ by the specified factor and preserving the other registers and the configuration invariant.

**Proof.** The machine first copies register $7$ into register $11$, leaving register $7$ unchanged. The register-copy loop (`Complexity.LogProg.registerCopy_loop`) applies because register $11$ starts at zero, hence is no larger than register $7$. Next it clears register $7$. The scale loop (`Complexity.LogProg.registerScale_loop`) repeatedly decreases register $11$ by one and increments register $7$ by the factor $C$ or $2C+3$, according to the outer flag. It therefore terminates with register $11$ zero and register $7$ equal to the original value of register $7$ times that factor. The assumed product bound ensures the incremented values stay within $B$; intermediate register updates are bounded by `Complexity.LogProg.register_update_le`. The machine's instruction invariant is supplied by `Complexity.comp_preS`. Concatenating the copy and scaling runs, and including the clearing step by `Complexity.LogProg.AReach.step`, gives the stated reachability and final register assignment.

**Key facts.** `Complexity.LogProg.registerCopy_loop`, `Complexity.LogProg.registerScale_loop`, `Complexity.LogProg.register_update_le`, `Complexity.comp_preS`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`.
