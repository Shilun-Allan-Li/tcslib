<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean :: Complexity.LogProg.eqCfg_read₂ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Second Register

**Claim.** After both distinct register heads are placed at position $k$, the symbol scanned at the second head is the content of register $r_2$ at cell $k$ in the original configuration.

**Proof.** The repositioning leaves the tape contents unchanged and assigns position $k$ to the head of $r_2$. Thus the scanned symbol is the original content of that tape at cell $k$. The update at the distinct register $r_1$ does not alter the second head's position.
