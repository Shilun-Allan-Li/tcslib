<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.csPrefix_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting-sort prefix phase

**Claim.** Under the stated counting-sort hypotheses and initial frequency counters, the prefix-sum program executes with cost at most $25N+6$, ends with index $N$, records cumulative frequencies in the counters, and preserves memory outside the destination and counter intervals.

**Proof.** Apply the pass-loop execution theorem (Ends.csFor) with invariant that after processing $r$ buckets, counter $t$ contains the number of items with key less than $t$ for every $t\le r$, while the unprocessed bucket counters still contain their original frequencies. Initially this follows from the frequency-counter invariant (CsSummed.start). In the round for bucket $t<N$, the current counter at $t$ is the number of items with key less than $t$, and the counter at $t+1$ is the frequency of key $t$ (the two parts of the invariant). Their sum is the number of items with key less than $t+1$ (cntLt_succ_left). The program writes this sum to counter $t+1$, establishing the invariant at the next stage (CsSummed.succ). Since the write lies in the counter interval, memory agreement outside the destination and counter intervals is preserved (SameOutside2.update). The loop theorem gives the endpoint at $N$ and the cost bound.

**Key facts.** `Light.CsSummed.start`, `Light.Ends.csFor`, `Light.cntLt_succ_left`, `Light.CsSummed.succ`, `Light.SameOutside2.update`.
