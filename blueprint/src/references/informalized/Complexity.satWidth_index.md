<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satWidth_index -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Index Bits Preserve the Width State

**Claim.** Folding the width-pass transition over $n$ consecutive one bits from state $2$, counter $c$, and flag $g$ leaves all three unchanged.

**Proof.** Induct on $n$. With no bits, the fold leaves its starting state unchanged. For the inductive step, the first one bit is processed in state $2$: the syntax transition stays in state $2$, and the counter and flag are preserved. The remaining $n$ one bits therefore leave that same triple unchanged by the induction hypothesis.
