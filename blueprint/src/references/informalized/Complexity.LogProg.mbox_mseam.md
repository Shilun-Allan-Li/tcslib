<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.mbox_mseam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for the initial compiled configuration

**Claim.** The initial compiled configuration has every register head in $[-1,W]$, every decider-work-tape head of absolute position at most $B$, and memory-head position of absolute value at most $P$, provided $|p|\le P$.

**Proof.** In the initial configuration, each register head is at position $0$, and the seam construction gives each decider-work-tape head position $0$. Since $-1\le 0\le W$ and $|0|\le B$, these satisfy the first two bounds. The appended memory head is at position $p$, so its bound is the hypothesis $|p|\le P$.
