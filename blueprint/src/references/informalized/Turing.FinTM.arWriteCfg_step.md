<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arWriteCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Write-sweep decrement step

**Claim.** For a nonzero sweep counter $j$, one simulator step from the write-sweep configuration at $j$ gives the write-sweep configuration at $j-1$.

**Proof.** Since $j\ne0$, the pending-write transition takes its nonzero-counter branch. It writes the encoded pending symbol into block position $j$, moves each work-tape head one cell to the left, and decreases the counter to $j-1$. The tape identity needed here is the tail-update fact (`Turing.FinTM.arTail_update`): writing that encoded symbol at position $j$ in the tape whose unprocessed tail begins after $j$ produces exactly the tail associated with counter $j-1$. The input head and output do not change, and the state remains the same pending write action. The head-position formula also agrees, since moving left from the encoded position for counter $j$ gives the encoded position for counter $j-1$. Thus all configuration components agree.

**Key facts.** `Turing.FinTM.arTail_update`.
