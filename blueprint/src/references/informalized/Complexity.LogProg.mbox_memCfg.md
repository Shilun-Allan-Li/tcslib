<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.mbox_memCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds after appending memory

**Claim.** Appending a memory tape with head position $p$ to a configuration preserves the given bounds on its first $m$ work-tape heads and next $k_D$ work-tape heads, and gives the new memory head absolute position at most $P$.

**Proof.** The configuration formed by appending a memory tape retains the original work-tape positions at every earlier index, while its final head position is $p$. Thus the first two bounds follow directly from the assumed bounds on $c$, and the last bound is exactly $|p|\le P$.
