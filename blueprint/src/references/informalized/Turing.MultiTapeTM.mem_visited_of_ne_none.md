<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.mem_visited_of_ne_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Cells Contain All Nonblank Symbols

**Claim.** If a work-tape cell contains a symbol after $t$ steps from the initial configuration, then the tape head occupied that cell at some time from $0$ through $t$.

**Proof.** Consider the sequence of configurations obtained by running the machine from its initial configuration, indexed by time. Initially every work-tape cell is blank. Between each consecutive pair of configurations, either the machine is halted and the configuration stays fixed, or the next configuration is obtained by applying one action. The general visited-cell lemma (`Turing.MultiTapeTM.ConfigCount.mem_image_workTapePos_of_ne_none`) says that for any such sequence, a cell that is nonblank at time $t$ must equal the head position at some time in the range $0$ through $t$. Applying it to this run yields the desired membership in the set of visited head positions.

**Key facts.** `Turing.MultiTapeTM.ConfigCount.mem_image_workTapePos_of_ne_none`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
