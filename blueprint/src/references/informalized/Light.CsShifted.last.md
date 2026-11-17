<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsShifted.last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final counter shift

**Claim.** From the shifted-state invariant at stage zero and agreement outside the destination and counter ranges, setting the first counter cell to zero yields the postcondition: all items remain placed, every counter start has its required key-below count, and outside those ranges the memory still agrees with the initial memory.

**Proof.** The placement condition survives changing counter cell $A.cnt$: the fact `CsShifted.placed_update` says that updating a counter cell at offset $t\le A.nb$ leaves every placed item unchanged, and we apply it with $t=0$ and value zero. For the counter starts, offset zero must contain the number of keys below zero, which is zero; the update sets it to zero. At any positive offset $t\le A.nb$, the update does not change that cell, and the shifted-state moved condition gives its value as the number of keys below $t$. Finally, the update is within the counter range, so the agreement outside the destination and counter ranges is preserved by `SameOutside2.update`.

**Key facts.** `Light.CsShifted.placed_update`, `Light.SameOutside2.update`.
