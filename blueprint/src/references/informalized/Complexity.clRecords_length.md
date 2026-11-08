<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRecords_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the trajectory prefix

**Claim.** For every $t\le T+1$, the first $t$ serialized trajectory rows have length at most $t$ times the number of movement-count fields times $2T+2$.

**Proof.** Proceed by induction on $t$. For $t=0$, the trajectory prefix is empty. For the successor step, the induction hypothesis bounds the first $t$ rows. Each movement count at time $t$ is at most $t$ (`Complexity.clCounts_bound`), hence at most $T+1$; its binary representation has length at most $T+1$ by the elapsed-count width bound (`Complexity.clElapsed_width`). The row-prefix length estimate (`Complexity.clRowPrefix_length`) then bounds the new row by the number of fields times $2(T+1)+2=2T+4$. Adding this to the previous bound and using the induction hypothesis gives the stated successor bound after routine arithmetic.

**Key facts.** `Complexity.clCounts_bound`, `Complexity.clElapsed_width`, `Complexity.clRowPrefix_length`.
