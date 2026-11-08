<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arTM_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulator space bound

**Claim.** Through time $t$, the simulator uses at most $(N+1)$ times the source machine's space through time $t+1$, plus the number $k$ of work tapes.

**Proof.** Fix a work tape. Every simulator head position visited by time $t$ has, by the position lemma (`arTM_position_visited`), the form of a block offset based at a source head position visited by time at most $t+1$. The offset bound places it inside that source position's block interval. Thus the simulator's visited positions are contained in the union of blocks over source visited positions. Cardinality is monotone under inclusion, and the block-cover bound (`arSpaceCover_card`) shows that this union has size at most $(N+1)$ times the source's distinct visited positions on this tape, plus one. Sum this inequality over all $k$ tapes. The sum of the source per-tape space counts is the source total space, while the added one on each tape sums to $k$, giving the claimed bound.

**Key facts.** `Turing.FinTM.arTM_position_visited`, `Turing.FinTM.arSpaceCover_card`.
