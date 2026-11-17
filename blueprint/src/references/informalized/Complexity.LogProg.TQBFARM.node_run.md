<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.node_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run through a quantified node

**Claim.** Starting at a node with depth $k$, stack value $S$, and pointer $p$, the machine reaches the first node-reading state with pointer $2k$ and all scratch registers zero, while satisfying the guard throughout.

**Proof.** First take the single instruction at the node label, which clears the pointer. The initial register bounds needed for this step follow from $2k\le B$, $S\le B$, and $p\le B$; `stp_bd` packages these coordinatewise bounds. From the resulting state, use the copy-loop result (`Complexity.LogProg.TQBFARM.cp_run`) for the first copy site: it adds $k$ to the cleared pointer, leaving pointer $k$, and exits to the second copy site. The copy loop preserves the guard. Apply the same result at the second site to add another $k$, reaching pointer $2k$ and the label `nd1`. In both applications the scratch register $Z$ starts at zero and the destination-plus-source bound follows from $2k\le B$. The intermediate states are joined by the reachability composition property (`Complexity.LogProg.AReach.trans`); `cont` identifies states with equal register records, and `fin_of` supplies the final unchanged-state step at `nd1`.

**Key facts.** `Complexity.LogProg.TQBFARM.stp_bd`, `Complexity.LogProg.TQBFARM.step_of`, `Complexity.LogProg.TQBFARM.cont`, `Complexity.LogProg.TQBFARM.cp_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.TQBFARM.fin_of`.
