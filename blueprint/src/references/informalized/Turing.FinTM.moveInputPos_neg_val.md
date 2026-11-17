<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.moveInputPos_neg_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value After a Clamped Left Move

**Claim.** For every $n$ and every valid input-head position $p$, moving one step left with clamping gives a position whose value is $p.val-1$, equivalently $\max(p.val-1,0)$.

**Proof.** Split into the boundary case $p=0$ and the case $p\ne0$. At the boundary, the clamped left move stays at zero, which agrees with truncated natural subtraction $0-1=0$. Otherwise, `moveInputPos_neg_of_ne_left` identifies the moved position with the valid position whose value is $p.val-1$; taking values gives the result.

**Key facts.** `Turing.moveInputPos_neg_of_ne_left`.
