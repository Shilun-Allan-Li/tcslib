<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleBack_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward oracle walk

**Claim.** Under the stated side condition on $p$, for every $u\le |p|-1$, the backward-dispatch run from the given configuration has unchanged input head, output, and state, with work-tape position $\epsilon_s(1+u)$, where $\epsilon_s$ is $1$ for the nonnegative side and $-1$ for the nonpositive side.

**Proof.** Let $m=1$ on the nonnegative side and $m=-1$ on the nonpositive side. The side condition gives $p=m|p|$ (Turing.oracleSide_distance). Along the proposed walk, at step $u$ the moving head is at $m+mu$. For each $u<|p|-1$, this position is not $p$: the equality would force the walk to have reached the bookmarked point before the final step, contrary to the distance from the origin. Because the head has not reached the bookmark, the marked tape cell is not read as the stopping marker. Thus the transition remains the backward-dispatch walk action, moving both relevant heads by $m$ while leaving state, input position, tape contents, and output unchanged. The general walk lemma (Turing.oracleWalk_run) iterates exactly these transitions up to $|p|-1$ steps. Finally, identifying its walking configurations with the stated bookmarked configurations gives the claimed run equality.

**Key facts.** `Turing.oracleSide_distance`, `Turing.oracleWalk_run`.
