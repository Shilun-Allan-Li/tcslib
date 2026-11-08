<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arMoveCfg_position -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Positions During the Move Sweep

**Claim.** During a move sweep, each work-tape head position can be expressed within the block of either its original position or its position after the action, with an offset at most $N+1$.

**Proof.** The sweep counter satisfies $r\le N+1$. Split according to the action's movement on tape $i$. If the movement is negative, the sweep position equals the block of the post-action head position with offset $r$. If the movement is zero, it is the original head's block at offset zero. If the movement is positive, it is the original head's block at offset $N+1-r$. The counter bound ensures these offsets are all at most $N+1$, giving the required alternative in each case.
