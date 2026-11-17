<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.incrementTM_spaceUsedByTape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Used by the Increment Machine

**Claim.** At every time, the increment machine visits at most $|w_i|+2$ cells on the selected tape, and exactly one cell on each other tape.

**Proof.** Decompose the selected word into $p$ leading true bits and either no remainder or a false bit followed by a tail (`catalog_increment_split`); in either case $p\leq |w_i|$. The trace formula (`catalog_increment_trace`) describes the head positions at every time. In its forward and return portions, the selected head stays within the interval from one cell left of its initial position to $p$ cells to its right. Hence all visited positions lie in an interval containing at most $p+2$ integer cells. The general interval bound for visited cells (`catalog_space_bound`) gives at most $p+2$, which is at most $|w_i|+2$. For any other tape the trace shows that its head never moves from its initial position, which is zero in the initial word configuration. The fixed-head space result (`catalog_space_one`) therefore gives exactly one visited cell.

**Key facts.** `Turing.catalog_increment_split`, `Turing.catalog_increment_trace`, `Turing.catalog_space_bound`, `Turing.catalog_space_one`.
