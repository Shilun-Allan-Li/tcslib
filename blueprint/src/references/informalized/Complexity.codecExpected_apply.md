<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecExpected_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected encoding of an action

**Claim.** Under the stated alignment of the encoded input-head and work-head positions with the configuration, every codec bit's expected value under the wired action inputs equals its observed value after applying the action to the configuration with its output replaced by the encoding of its output summary.

**Proof.** Proceed by the cases defining a codec bit. Input bits are copied from the old-bit port, and state bits are determined directly by the action's state, so these cases agree by definition. For an input-head bit, the encoded row position equals the given position $p$, so the expected moved position agrees with the moved configuration position. For summary bits, the summary flags read from the row recover the configuration's output summary (`Complexity.codecReadSummary_flags`); appending the action's output and summarizing therefore gives precisely the observed summary. Finally consider a work-tape bit. Its three possible tags record, respectively, whether the cell contains false, whether it contains true, or whether the head is at that cell. The head-alignment hypothesis identifies the encoded head position with the configuration's actual position. If the action does not write at the head, the old cell value is retained; if it writes, the updated cell has the written value. In either case the expected cell flags match the observed ones. For the head tag, moving the aligned encoded position by the action's displacement gives the actual new head position, so the flags agree here as well.

**Key facts.** `Complexity.codecReadSummary_flags`.
