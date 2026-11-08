<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsShifted.placed_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Placement survives a counter update

**Claim.** Changing any counter cell at offset $t\le A.nb$ leaves every item at its prescribed destination position.

**Proof.** Fix an item index $j<A.n$. Its sort position satisfies $\mathrm{sortPos}(kf,A.n,j)<A.n$ by `sortPos_lt`. Thus its destination address lies in the destination range. The destination and counter ranges are apart by the layout precondition, so this address cannot equal the counter address $A.cnt+t$. The update therefore leaves the memory value at the item's destination unchanged, and the shifted-state placement condition supplies the required item value.

**Key facts.** `Light.sortPos_lt`.
