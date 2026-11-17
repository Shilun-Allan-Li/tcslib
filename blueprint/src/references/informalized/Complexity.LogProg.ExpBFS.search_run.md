<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Search.lean :: Complexity.LogProg.ExpBFS.search_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Reachability Search

**Claim.** Starting with the specified zeroed registers and fresh memory cells, the machine reaches the appropriate count-comparison label. At that point, $U=S.K$, $c$ counts exactly the indices below $S.K$ reachable from a true initial query by true step queries that stay below $S.K$, and the other registers retain their values from $S$. The resulting memory extends the original marks, changes no cells outside the designated region, and marks precisely those reachable indices within it.

**Proof.** First run the initial-marking search. The initial-search result (`ini_run`) preserves existing marks, marks every index below $S.K$ with a true initial query, and leaves other cells of the bounded region unmarked because those cells were fresh. Next, run the relaxation rounds (`rounds_run`) from this initialized tape. Its closure property says that every new mark is supported by a true step query from an already marked index, and its propagation property says that a marked index with a true step query to another index below $S.K$ causes that target to be marked. Together these give the two directions of the reachability characterization: by induction along the rounds, every marked index is reachable; by induction along a finite reachability path, every reachable index is eventually marked. The latter induction begins with the initial marks and extends each path by one step using `Cl.step`, the fact that a reachable index remains reachable after a valid true step.

The rounds preserve monotonicity of memory and leave cells outside the designated region unchanged (`Mono.trans`, `Out.trans`). The reachability equivalence therefore holds for the tape $M_2$ after the rounds. Finally, run the counting scan (`count_run`) from $U=0$ with $c=0$. It counts exactly the marked indices below $S.K$. The reachability equivalence identifies this count with the stated filtered cardinality, and `reach_cf` aligns the resulting configuration with the desired record of register values and comparison label. The initial-search and round runs concatenate with this final scan to give the required finite guarded run.

**Key facts.** `Complexity.LogProg.ExpBFS.ini_run`, `Complexity.LogProg.ExpBFS.rounds_run`, `Complexity.LogProg.ExpBFS.Cl.step`, `Complexity.LogProg.ExpBFS.Mono.trans`, `Complexity.LogProg.ExpBFS.Out.trans`, `Complexity.LogProg.ExpBFS.count_run`, `Complexity.LogProg.ExpBFS.reach_cf`.
