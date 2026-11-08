<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.ConfigCount.mem_image_workTapePos_of_ne_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Occupied cells lie among visited head positions

**Claim.** If all work-tape cells are blank initially and each successive configuration is either unchanged or obtained by applying one action, then any cell containing a symbol at time $t$ is among the head positions visited on that tape through time $t$.

**Proof.** Induct on $t$. At time zero the hypothesis that every cell is blank rules out an occupied cell. For the successor step, if the configuration is unchanged, the occupied cell was already occupied at time $t$, so the induction hypothesis gives an earlier visit. If an action is applied, consider its action on the tape in question. When it makes no write, the cell's contents are unchanged, and the induction hypothesis again applies. When it writes a symbol, the tape contents change only at the old head position. If the occupied cell is that position, it was visited at time $t$; otherwise its contents are unchanged and an earlier visit follows by induction. In each case the relevant time is at most $t+1$, as required.
