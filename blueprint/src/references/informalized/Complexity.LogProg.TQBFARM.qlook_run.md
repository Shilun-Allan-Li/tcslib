<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.qlook_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quantifier Lookup Run

**Claim.** For either Boolean value $v$, if $2k\le B$ and $S\le B$, the program can run from the first copy phase of the return procedure at depth $k$ and stack value $S$ to the quantifier-reading state with the same depth and stack value and pointer $2k$. The scratch registers are zero at the endpoints, and the run stays within the register bound and precondition.

**Proof.** First, the copy-loop result for the first return phase says that copying the depth $k$ into the pointer, starting with zero pointer and scratch registers, reaches the second return-copy phase with pointer $k$; the copied destination and source sum is at most $B$, since $2k\le B$. The register bounds needed for that loop follow from $k\le B$, $S\le B$, and the initial zero values. Next, apply the same copy-loop result to the second phase: it adds another $k$ to the pointer and reaches the quantifier-reading state, with pointer $2k$. This second loop has the same source and destination bounds. The two bounded, precondition-preserving reaches concatenate by transitivity of reachability (\texttt{Complexity.LogProg.AReach.trans}). The endpoint states agree with the stipulated state having unchanged depth and stack and pointer $2k$; the scratch registers are again zero. The state-identification steps use the equality-transport reachability fact (\texttt{Complexity.LogProg.TQBFARM.cont}) between the two copy phases and the endpoint, and the zero-length reachability fact (\texttt{Complexity.LogProg.TQBFARM.fin_of}) to identify the final state.

**Key facts.** `Complexity.LogProg.TQBFARM.stp_bd`, `Complexity.LogProg.TQBFARM.cp_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.TQBFARM.cont`, `Complexity.LogProg.TQBFARM.fin_of`.
