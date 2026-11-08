<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsShifted.start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial shifted-state invariant

**Claim.** If the placement invariant holds after all $A.n$ items have been placed, then the shifted-state conditions hold at stage $A.nb$.

**Proof.** The placed-item condition is exactly the placement invariant's condition for all indices below $A.n$. The moved-cell condition requires an offset $t$ with $A.nb<t$, while also assuming $t\le A.nb$; no such offset exists, so this condition is vacuous. For each $t<A.nb$, the placement invariant says that the counter at offset $t$ contains the number of keys below $t$ plus the number equal to $t$ among the first $A.n$ indices. By the key-count partition identity `cntLt_succ_left`, this sum is the number of keys below $t+1$. That is precisely the shifted-state waiting-cell requirement.

**Key facts.** `Light.cntLt_succ_left`.
