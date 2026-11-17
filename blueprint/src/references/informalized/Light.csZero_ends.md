<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.csZero_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting-sort counter initialization

**Claim.** From a state with arbitrary loop variables and memory agreeing with the initial memory outside the destination and counter ranges, counter initialization terminates within cost $15N+23$, sets the loop index to $N+1$, zeros counter cells $0$ through $N$, and preserves memory agreement outside those ranges.

**Proof.** The initial state has no assumed counter contents, so it satisfies the zeroed-prefix condition for the empty prefix vacuously. The state can therefore be regarded as the starting case of the counted-loop execution (`CsState.imp`). For each index $t<N+1$, write zero to counter cell $A.cnt+t$. This extends the zeroed prefix by one cell (`CsZeroed.succ`); since the write lies inside the counter range, agreement outside the destination and counter ranges is preserved (`SameOutside2.update`). Iterating this argument through all $N+1$ counter cells yields the final index and zeroed-prefix property, with the stated cost bound supplied by the counted-loop execution lemma (`Ends.csFor`).

**Key facts.** `Light.CsState.imp`, `Light.CsZeroed.succ`, `Light.SameOutside2.update`, `Light.Ends.csFor`.
