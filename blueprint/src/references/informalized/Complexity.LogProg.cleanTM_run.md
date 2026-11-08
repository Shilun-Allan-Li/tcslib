<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean :: Complexity.LogProg.cleanTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Simulation with Tape Erasure

**Claim.** Under the stated halting and visited-cell bounds, the cleaning machine eventually reproduces the original machine's output, halts with blank work tapes and heads at the origin, and keeps every head within absolute position $s$.

**Proof.** Let $T_0$ be the first time the original machine reaches the halting state. Such a time exists since it halts at time $T$, and $T_0\le T$. Once halted, the machine remains in the same configuration, so its configuration at $T$ equals its configuration at $T_0$ (`runFrom_add`, `runFrom_of_halt`).

For each tape, every position visited by time $T_0$ belongs to the visited set by time $T$. A visited position $z$ has $|z|$ strictly less than the cardinality of the visited set (`abs_pos_lt_card_visited`); the assumed cardinality bound therefore gives $|z|+1\le s$. In particular, the simulation's head positions remain within the bound. Before the first halt, the cleaning machine faithfully simulates each step of the original machine: induction on time uses the fact that a live simulation state steps to the next simulated configuration (`sim_step_clean`). The initialization step enters this simulation (`init_step`).

At time $T_0$, consider each original tape's visited positions. They form an interval $[a,b]$ containing the origin, with both endpoints visited (`visited_interval`). The head is in that interval, and the visited-position bound puts the endpoints within the required margins of $s$. The tape-support condition follows because every nonblank cell lies among the visited positions (`mem_visited_of_ne_none`). The auxiliary tape has marked the visited interval, with the current head position included; inserting that position recovers the full visited set, and updating the mark at the head establishes the required tape initialization using `wr_markSet`.

The staged cleaning procedure now erases each tape and restores its head to the origin. The stage result (`stages_run`) supplies a finite duration and the head bound throughout; after all $k$ stages, the configuration has both tape families blank and all heads at zero. Combining the initialization step, the simulation interval, and the cleaning interval gives a total time at which the cleaning machine halts. The bound throughout the concatenated run follows by applying `runFrom_forall_append` to the intervals: the initial configuration and simulated configurations satisfy the bound via `PB_ccfg`, the simulation head positions are visited by time $T_0$, and the cleaning stages satisfy the bound supplied by `stages_run`. Finally, the output is unchanged during cleaning, and the original output at $T_0$ equals its output at $T$ because the original machine has halted.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.abs_pos_lt_card_visited`, `Turing.MultiTapeTM.visitedByTapeHead_mono`, `Complexity.LogProg.sim_step_clean`, `Complexity.LogProg.init_step`, `Complexity.LogProg.visited_interval`, `Turing.MultiTapeTM.mem_visited_of_ne_none`, `Complexity.LogProg.wr_markSet`, `Complexity.LogProg.stages_run`, `Complexity.LogProg.PB_ccfg`, `Complexity.LogProg.runFrom_forall_append`.
