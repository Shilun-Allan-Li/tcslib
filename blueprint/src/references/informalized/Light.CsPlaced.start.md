<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsPlaced.start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial placement state

**Claim.** If the summed-state invariant holds at the key bound $A.nb$, then the placement-state invariant holds for zero placed items.

**Proof.** For any $t<A.nb$, the summed-state starting condition at $t$ gives the required value of the counter cell. The placement invariant asks for this value plus the number of indices below zero with key $t$; that count is zero. Its placement condition concerns indices $j<0$, of which there are none, so it holds vacuously.
