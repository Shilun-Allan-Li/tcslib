<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.read_row -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading one tape row

**Claim.** Processing the block at coordinate $j$ whose left-neighbour flags are initially false updates the control table from its value at $j$ to its value at $j+1$, and records the left-neighbour head flags in the block.

**Proof.** Unfold the row and visit descriptions, then apply the indexed block-fold identity (`indexedFold_block`): each tape's cell is visited using that tape's own control entry, so the final control table and output row can be checked tape by tape. Fix a tape index. If its head is at $j$, the visit reads the cell symbol at that location and places the corresponding head flag in the updated control entry; this agrees with the control table at $j+1$. If its head is not at $j$, the visit retains the prior symbol information, and the condition that the head lies strictly left of $j+1$ is equivalent to lying strictly left of $j$. In either case the block's left-neighbour flag is set to indicate whether the head was at $j-1$. These coordinate checks establish the asserted control table and row; the row equality itself follows directly from the visit rule.

**Key facts.** `Turing.FinTM.indexedFold_block`.
