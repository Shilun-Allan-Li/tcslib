<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satDrop_dispatch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatch to the copy phase

**Claim.** For any Boolean input word $x$ and natural numbers $p,n$, one step from state $4$ at the clamped offset $p$, with a unary counter of length $n$ and head at $n$ and empty output, gives state $5$ at the same offset with the counter, head, and output unchanged.

**Proof.** At counter position $n$, the unary counter has no symbol: its ones occupy positions strictly below $n$. This is the counter-read fact Complexity.satRedCounter_read. Thus the state-$4$ transition takes the dispatch branch leading to state $5$, with no output and no counter action. The input-head movement is zero, so the clamped offset is unchanged by Turing.moveInputPos_zero; the counter-head movement is also zero. The resulting configuration equality follows from the transition's configuration description (Complexity.satDrop_move).

**Key facts.** `Complexity.satRedCounter_read`, `Turing.moveInputPos_zero`, `Complexity.satDrop_move`.
