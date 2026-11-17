<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_seek_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter-Program Search Run

**Claim.** The search state scans the indicated register interval, reaching the appropriate hit state when the query position lies within it and otherwise reaching the specified miss or separator state; the endpoint register values and all intermediate bounds are as stated.

**Proof.** Apply the indexed-search loop theorem (`indexedSeek_loop`) to the machine's search, probe, increment, and walk states. Here the pointer is register $0$, the endpoint is register $3$ for a suffix search and register $11$ for a prefix search, the scanned index is register $13$, and the target is register $5$. The program tests whether the current index equals the target; on a miss it increments the index and advances the pointer by the prescribed stride, then repeats. The stride is $2$ for suffix search and $1$ for prefix search, matching the machine's walk transitions. The endpoint identity supplies the interval length, while the register bounds and $v_{13}+N\le B$ ensure that each intermediate increment stays within the bound. Thus, if $v_5<v_{13}+N$, the scan stops at the target and reaches the appropriate hit state with pointer advanced by the stride times $v_5-v_{13}$. Otherwise it exhausts the interval and reaches the false-answer state for suffix search or the separator state for prefix search, with pointer at the endpoint. The loop theorem also certifies precondition validity and the bound on every preceding configuration.

**Key facts.** `Complexity.LogProg.indexedSeek_loop`.
