<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.nbox_seam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial configuration satisfies tape bounds

**Claim.** Adjoining blank auxiliary tapes to the initial arithmetic configuration gives a configuration whose program-tape head positions lie between $-1$ and $W$, and whose auxiliary-tape head positions have absolute value at most $B$.

**Proof.** In the initial arithmetic configuration, each program-tape head position is the initial position, which lies between $-1$ and $W$; adjoining the auxiliary tapes does not change those positions. Each auxiliary tape is assigned head position $0$, whose absolute value is at most the natural number $B$. Hence both required bounds hold.
