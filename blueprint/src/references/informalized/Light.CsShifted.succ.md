<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsShifted.succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Predecessor Shifted-State Invariant

**Claim.** Under the count-sort layout assumptions, if the shifted-state conditions hold at stage $s+1$, then setting the counter cell at offset $s+1$ to the number of keys below $s+1$ gives the shifted-state conditions at stage $s$.

**Proof.** The item placements remain valid after the update: the counter cell being changed is disjoint from the destination range, so the placed-item equations are unchanged. For a counter offset $t$ with $s<t\le N_b$, the update is at a different cell, and the old moved condition at stage $s+1$ supplies the required count of keys below $t$. At the boundary $t=s+1$, the update itself assigns exactly the count of keys below $s+1$. Finally, if $t<s$, then the update is again at a different cell, and the old waiting condition gives the count of keys below $t+1$, as required.

**Key facts.** `Light.CsShifted.placed_update`.
