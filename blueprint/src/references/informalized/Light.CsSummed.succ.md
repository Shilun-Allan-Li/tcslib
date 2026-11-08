<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsSummed.succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Summed-Counter Invariant

**Claim.** If the summed-counter conditions hold at stage $r$, then setting the counter cell at offset $r+1$ to the number of keys below $r+1$ makes them hold at stage $r+1$.

**Proof.** Consider first an offset $t\le r+1$. If $t<r+1$, then the update affects a different cell, and the old start condition gives the required number of keys below $t$. If $t=r+1$, the updated cell has been assigned precisely the number of keys below $r+1$. These are all the new start conditions. For the size conditions, take $t<N_b$ with $r+1\le t$. The updated offset $r+1$ is distinct from $t+1$, so that cell retains its old value; the old size condition applies because $r\le t$, and gives the required number of keys equal to $t$.
