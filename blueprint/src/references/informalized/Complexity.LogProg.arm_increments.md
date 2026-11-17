<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.arm_increments -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability by repeated increments

**Claim.** If each of $k$ consecutive program states increments register $r$, and all registers start within $B$ with enough room for the $k$ increments of $r$, then the program reaches the state after those instructions with $r$ increased by $k$, while maintaining the stated precondition and register bound at every earlier step.

**Proof.** Apply the repeated-chain reachability result (`arm_chain`) in its increment case. At each of the $k$ transitions, the instruction increments register $r$ and advances from label $i$ to label $i+1$. After $i$ such transitions, the valuation agrees with the initial valuation except that $r$ has increased by $i$; every register remains at most $B$, since the other registers are unchanged and $v(r)+i\le v(r)+k\le B$. The side condition is therefore preserved at each preceding configuration, and after all $k$ transitions the state is $\ell_k$ with the required updated valuation and no answer yet.

**Key facts.** `Complexity.LogProg.arm_chain`.
