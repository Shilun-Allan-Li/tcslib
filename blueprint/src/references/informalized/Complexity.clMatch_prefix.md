<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatch_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Scan Records Comparison Flags

**Claim.** For each $j\le N$, the matcher reaches a configuration representing the first $j$ rows: its candidates are empty when $j=0$ and otherwise contain row $j-1$, its cursor is at the end of the packed first $j$ rows, its clock position is $j$, and its flags record the comparisons for rows $0$ through $j-1$. This occurs within the stated time bound, and the target words remain unchanged.

**Proof.** Proceed by induction on $j$. For $j=0$, take time zero. The stream cursor and clock position are both zero, the flag list is empty, and the prior row is empty, so the claimed configuration is the initial one.

For the successor step, suppose $j+1\le N$. By induction, after some time $a$ within the bound for $j$, the matcher is at the claimed configuration for the first $j$ rows. The width bound needed for the next round holds for the current candidates: if $j=0$ they are empty, and otherwise they are row $j-1$, whose index is less than $N$. The new row $j$ also satisfies the width bound, as do the target words. Split the packed stream of the first $N$ rows after the packed first $j$ rows and the packed fields of row $j$; the remainder is the untouched suffix. The one-round result (`Complexity.clMatch_round`) now supplies a time $b\le l(5W+7)+2W+5$ that loads row $j$, advances the cursor past its packed fields, advances the clock to $j+1$, and appends exactly its comparison flag.

Run the induction segment followed by this round. The run-composition law (`Turing.MultiTapeTM.runFrom_add`) identifies the resulting configuration with the desired one. The time is at most $jB+B=(j+1)B$, where $B=l(5W+7)+2W+5$. The list identities for the prior row, packed rows, and appended flags give the claimed configuration at $j+1$.

**Key facts.** `Complexity.clMatch_round`, `Complexity.clRows_split`, `Turing.MultiTapeTM.runFrom_add`.
