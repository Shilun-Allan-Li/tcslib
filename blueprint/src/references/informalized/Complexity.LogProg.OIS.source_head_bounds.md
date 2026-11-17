<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.source_head_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Head Bounds from Space

**Claim.** At every step $n\le t$, each work-tape head lies between minus the total space used through step $t$ and that total space used.

**Proof.** Fix a tape and let $z$ be its head position after step $n$. By definition, that position belongs to the set of positions visited by the tape head through step $n$. Since $n\le t$, the visited set through step $n$ is contained in the visited set through step $t$ (`Turing.MultiTapeTM.visitedByTapeHead_mono`). The absolute-position bound for a visited head position (`Turing.MultiTapeTM.abs_pos_lt_card_visited`) gives $|z|$ strictly less than the size of this latter set. Its size is at most the total space used through step $t$, since that total sums the visited-set sizes over all tapes. Thus $|z|$ is at most that total, which is equivalent to the claimed two-sided interval bound.

**Key facts.** `Turing.MultiTapeTM.visitedByTapeHead_mono`, `Turing.MultiTapeTM.abs_pos_lt_card_visited`.
