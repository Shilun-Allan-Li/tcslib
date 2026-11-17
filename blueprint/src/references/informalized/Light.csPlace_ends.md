<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.csPlace_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting-sort placement phase

**Claim.** Under the stated counting-sort hypotheses and cumulative-count and bucket-size conditions, the placement program executes with cost at most $38n+6$, places each processed item at its stable sorted position, updates the counters to the next positions, and preserves memory outside the destination and counter intervals.

**Proof.** Apply the pass-loop execution theorem (Ends.csFor) with invariant that, after processing $i$ items, each processed item $j<i$ is stored at its stable sorted position and counter $t$ records the next available position for key $t$. The initial cumulative counts and bucket sizes give this invariant before the first iteration (CsPlaced.start). In round $i<n$, the key expression is safe and evaluates to $kf(i)$ (csKey_gives). The current counter for that key equals $\mathrm{sortPos}(kf,n,i)$ by the invariant; this position is in the destination interval (sortPos_lt). The source cell still contains item $it(i)$ by the source-memory agreement (CountSort.Pre.item). The program therefore stores that item at the indicated destination position and increments the corresponding counter, establishing the invariant for $i+1$ (CsPlaced.succ). These stores affect only the destination or counter intervals, so agreement outside them is preserved (SameOutside2.update). The pass theorem yields the endpoint at index $n$ and the claimed cost bound.

**Key facts.** `Light.CsPlaced.start`, `Light.Ends.csFor`, `Light.csKey_gives`, `Light.sortPos_lt`, `Light.CountSort.Pre.item`, `Light.CsPlaced.succ`, `Light.SameOutside2.update`.
