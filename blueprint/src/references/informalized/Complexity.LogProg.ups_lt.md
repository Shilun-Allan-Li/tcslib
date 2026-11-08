<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathWalk.lean :: Complexity.LogProg.ups_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Less-than loop entry

**Claim.** If each iteration below the random index has the asserted semantics at the index routine, and each state at or beyond the random index has them at the continuation label, then the less-than loop entry has the same bounded-register termination and probabilities.

**Proof.** The loop first clears its counter, so it remains to establish the loop invariant at counter value $0$. Use strong induction on the remaining distance $n-a$, maintaining $a\le n$ and $a\le nx$. When the distance is zero, $a=n$; since $n\le nx$, the counter has reached or passed the random index, and the equality branch transfers the asserted property from the continuation label. For a positive remaining distance, the comparison with $n$ is unequal, so the loop tests whether $a=nx$. If they are equal, the equality branch transfers the property from the index routine, using $nx<n$. If they are unequal, the counter is incremented and the induction hypothesis applies to $a+1$: the remaining distance decreases by one, while the bounds on the counter persist. The equality and inequality branch principles (`PSem.jeq_pos` and `PSem.jeq_neg`), together with the increment principle (`PSem.inc`), carry the same semantics back through each iteration. The initial clear is handled by `PSem.clr`.

**Key facts.** `Complexity.LogProg.PSem.clr`, `Complexity.LogProg.PSem.jeq_pos`, `Complexity.LogProg.PSem.jeq_neg`, `Complexity.LogProg.PSem.inc`.
