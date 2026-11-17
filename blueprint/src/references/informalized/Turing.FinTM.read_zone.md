<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.read_zone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a tape zone

**Claim.** Processing the blocks at coordinates $j$ through $j+n-1$, with left-neighbour flags initially false, updates the control table from its value at $j$ to its value at $j+n$ and records the flags in those same blocks.

**Proof.** Induct on the number $n$ of blocks, generalizing the starting coordinate. For zero blocks, both the sweep and the zone are empty, so the control table and output are unchanged. For $n+1$, split the zone into its first row at $j$ and the remaining $n$ rows starting at $j+1$. Sweeping a concatenation is the same as sweeping the first part and then the second, concatenating their output rows (`sweepFold_append`). The one-row result (`read_row`) updates the table to its value at $j+1$ and records that row's flags. Apply the induction hypothesis to the remaining zone to update the table from $j+1$ to $j+1+n=j+(n+1)$ and record its flags. Together these are exactly the claimed zone output and final table.

**Key facts.** `Turing.FinTM.sweepFold_append`, `Turing.FinTM.read_row`.
