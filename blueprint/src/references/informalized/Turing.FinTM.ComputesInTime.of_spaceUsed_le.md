<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.FinTM.ComputesInTime.of_spaceUsed_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bounded by the Configuration Count

**Claim.** If the machine computes $w$ from $x$ within $t$ steps and uses at most $s$ work-tape cells during those steps, then it computes $w$ within $(|Q|+1)(|x|+2)3^{k(2s+1)}(2s+1)^k$ steps.

**Proof.** Let $T$ be the first time the run on $x$ is halted. Such a time exists because the run is halted by time $t$, and $T\leq t$. Every head position and every nonblank work-tape cell encountered through time $t$ lies among the visited cells of that tape. Each tape visits at most $s$ cells, since its visited-cell count is at most the total space use, which is at most $s$. The bound on the absolute value of a visited position by the number of visited cells (`abs_pos_lt_card_visited`), together with monotonicity of visited cells over time (`visitedByTapeHead_mono`) and the inclusion of nonblank cells among visited cells (`mem_visited_of_ne_none`), gives bounds of $s$ on these positions and cell locations throughout the run.

Encode each configuration's finite core using this bounded range. The encoding is injective on configurations satisfying those bounds: equal codes imply equal cores (`coreCode_inj`). Moreover, before the first halting time, no two configurations in the run can have the same core, since that would force a repeated configuration before halting (`core_injOn`). Thus the $T$ configurations at times $0,\ldots,T-1$ have distinct codes. Counting the possible codes—accounting for the state or halting marker, input-head position, work-tape contents, and work-head positions—gives $T\leq (|Q|+1)(|x|+2)3^{k(2s+1)}(2s+1)^k$.

The run is fixed once it reaches the halted configuration at time $T$. Since the displayed bound is at least $T$, running for that many steps gives the same halted configuration. Also, the run at the original time $t$ has that same configuration, because $T\leq t$. Its output is therefore still $w$, proving the required time-bounded computation. The equivalence between the computation definition and the halted-state/output conditions is used to extract and reassemble those conditions (`computesInTime_iff`).

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.spaceUsedByTape_le_spaceUsed`, `Turing.MultiTapeTM.abs_pos_lt_card_visited`, `Turing.MultiTapeTM.visitedByTapeHead_mono`, `Turing.MultiTapeTM.mem_visited_of_ne_none`, `Turing.MultiTapeTM.ConfigCount.coreCode_inj`, `Turing.MultiTapeTM.ConfigCount.core_injOn`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
