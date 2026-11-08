<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.exists_forall_not_of_randProb_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A String Avoiding Every Bad Event

**Claim.** If each fixed $n$-bit string has bad-event probability at most $\delta$ over uniformly chosen $m$-bit strings, and $2^n\delta<1$, then some $m$-bit string avoids the bad event for every $n$-bit string.

**Proof.** Suppose, to the contrary, that every $m$-bit string is bad for at least one choice of the $n$-bit string. The set of all $m$-bit strings is then covered by the union, over all $n$-bit strings $v$, of the strings bad for $v$. Counting this cover and bounding a union by the sum of its set sizes gives $2^m\leq\sum_v |\{r:\mathrm{Bad}(v,r)\}|$. For each $v$, the probability hypothesis says that this set has size at most $\delta 2^m$. There are $2^n$ choices of $v$, so the right side is at most $2^n\delta 2^m<2^m$, a contradiction. Here the count of bit strings of length $j$ is $2^j$ (`card_univ_bitstrings`).

**Key facts.** `Randomized.card_univ_bitstrings`.
