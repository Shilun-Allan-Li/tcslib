<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arSpaceCover_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block coverage cardinality bound

**Claim.** For a machine, configuration, work tape, and times and block parameter $N$, the union of the block intervals indexed by the visited head positions has cardinality at most $(N+1)$ times the number of distinct visited positions, plus one.

**Proof.** Proceed by induction on the time horizon. At time zero there is a single visited position, so its block has cardinality $N+2$, exactly the asserted bound. When the horizon grows by one, the visited-position set either already contains the new head position, in which case the union is unchanged, or gains that position. In the latter case, the preceding head position is among the old visited positions, and consecutive machine configurations move a work-tape head by at most one. The corresponding new block therefore intersects the old block at the preceding head position, by the neighboring-block intersection result (`arSpaceBlock_inter`). The new block has cardinality $N+2$ (`arSpaceBlock_card`), and the finite-set union formula says the union's cardinality increases by the new block's size minus the intersection's size. Since the intersection contains at least one point, this increase is at most $N+1$. The induction hypothesis then gives the desired bound with one additional distinct visited position.

**Key facts.** `Turing.FinTM.arSpaceBlock_card`, `Turing.FinTM.arSpaceBlock_inter`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.workTapePos_step_le`.
