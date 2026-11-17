<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsZeroed.succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extension of a Zeroed Counter Range

**Claim.** If the counter cells at offsets below $j$ vanish, then after setting the cell at offset $j$ to zero, all counter cells at offsets below $j+1$ vanish.

**Proof.** Take any $t<j+1$. Either $t<j$, in which case the update is at a different cell and the original vanishing condition still gives value zero, or $t=j$, in which case the update assigns zero directly. Thus every required cell in the extended range vanishes.
