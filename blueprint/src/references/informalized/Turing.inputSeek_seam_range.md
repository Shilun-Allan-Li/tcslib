<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputCall.lean :: Turing.inputSeek_seam_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Range Across a Seam

**Claim.** If the first machine reaches its exit state for the first time at time $t_1$, and both component runs keep each work-tape head within its specified interval, then the composite run keeps every work-tape head within that interval through time $t_1+1+t_2$.

**Proof.** Fix a time $u\le t_1+1+t_2$ and a tape $j$. The seam-visited-head inclusion (`seamCompTM_visitedByTapeHead_ofCfg`) says that the head position at this time in the composite run belongs to the union of positions visited by the first machine through time $t_1$ and positions visited by the second machine, started in its entry state, through time $t_2$. Thus it lies in one of those two sets. In the first case, the position is attained at some time $v\le t_1$, so the first run’s range hypothesis puts it in $[\ell_j,h_j]$. In the second case, it is attained at some time $v\le t_2$, and the second run’s range hypothesis gives the same conclusion. Hence the composite head position is in the required interval.

**Key facts.** `Turing.seamCompTM_visitedByTapeHead_ofCfg`.
