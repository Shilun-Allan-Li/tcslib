<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/WindowClock.lean :: Turing.FinTM.inWindow_of_spaceUsed_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bounds the Work-Tape Window

**Claim.** If the computation uses at most $s$ distinct work-tape cells through time $t$, then at every time $u\le t$ each work-tape head has absolute position at most $s$, and all cells whose positions have absolute value greater than $s$ are blank.

**Proof.** Fix a tape. Its visited positions through time $t$ form a finite set whose cardinality is at most the total space used: the per-tape space is bounded by total space (`spaceUsedByTape_le_spaceUsed`). Every visited position $z$ satisfies $|z|$ strictly less than the cardinality of this set (`abs_pos_lt_card_visited`), hence $|z|<s$. At time $u\le t$, the head position belongs to the visited set through time $t$, so its absolute value is at most $s$. Now take a position $z$ with $|z|>s$. If that cell were nonblank at time $u$, it would have been visited by the head by that time (`mem_visited_of_ne_none`), and therefore would belong to the visited set through time $t$ because visited sets grow with time (`visitedByTapeHead_mono`). The strict bound on visited positions would then contradict $|z|>s$. Thus every such cell is blank.

**Key facts.** `Turing.MultiTapeTM.spaceUsedByTape_le_spaceUsed`, `Turing.MultiTapeTM.abs_pos_lt_card_visited`, `Turing.MultiTapeTM.mem_visited_of_ne_none`, `Turing.MultiTapeTM.visitedByTapeHead_mono`.
