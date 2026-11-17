<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.csCount_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting-sort counting-loop execution

**Claim.** Under the counting-sort preconditions and the stated initial state and zero-counter conditions, the counting loop executes with cost at most $30n+6$, ends with index $n$, and records the frequency of each key in the designated counter cell while preserving memory outside the destination and counter intervals.

**Proof.** Use the loop execution theorem (Ends.csFor) with invariant that after processing $i$ items, counter zero is still zero and counter $t+1$ contains the number of processed items whose key is $t$. The initial state satisfies this invariant at $i=0$: the zeroed-counter condition implies that all the frequency counters are zero, which is the empty-prefix count. For a round at index $i<n$, the key expression is safe and evaluates to $kf(i)$ (csKey_gives); the precondition ensures this key is a valid bucket. The current value in its frequency cell is the count of earlier indices with that key, so incrementing that cell establishes the invariant for the first $i+1$ items (CsCounted.succ). The cell lies in the counter interval, so this update preserves agreement with the original memory outside the destination and counter intervals (SameOutside2.update). The loop theorem then supplies the endpoint at index $n$ and the stated cost bound.

**Key facts.** `Light.CsCounted.start`, `Light.Ends.csFor`, `Light.csKey_gives`, `Light.CsCounted.succ`, `Light.SameOutside2.update`.
