<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.write_row -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Sweep on One Tape Block

**Claim.** Sweeping backward through the reversed encoding of the tape cells at coordinate $j$, starting with the head flags at $j+1$, produces the head flags at $j$ and the reversed encoding of the action-updated configuration at $j$.

**Proof.** Expand the row and visit definitions. The reversed row is an indexed list of tape cells, each paired with its tape index. The indexed block-reversal lemma (`indexedFold_block_reverse`) evaluates the sweep independently at each index: the running flag is updated by that tape's visit rule, and the cell is replaced by its visited value. The final flag at index $i$ is the old head flag at $j$, as required. For the cell value, if the head was at $j$, the action's optional write is applied to the old symbol; otherwise the symbol is unchanged. This is exactly the tape-content rule for applying the action. For the neighboring-head flag, the visit rule carries the old flag from the appropriate neighboring coordinate according to whether the head moves left, stays, or moves right. That is precisely the new head position after the action. The final auxiliary flag is cleared, matching the unread row encoding. Hence the indexed cells, in their reversed order, agree with the claimed updated row.

**Key facts.** `Turing.FinTM.indexedFold_block_reverse`.
