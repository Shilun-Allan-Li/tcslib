<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.goldreichLevinActiveInvariant_retained -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of the Active Invariant

**Claim.** If the active family satisfies the invariant at stage $k$ and all candidate weight estimates are accurate within $\tau^2/4$, then the retained family satisfies the invariant at stage $k+1$.

**Proof.** Verify the three clauses of the invariant in order. First, every retained set is a candidate, and candidates lie inside the first $k+1$ coordinates whenever the old active sets lie inside the first $k$ coordinates (`goldreichLevinCandidates_subset_prefixCoordinates_succ`). Second, for any heavy frequency set, its length-$(k+1)$ prefix is retained: the stage-accuracy result gives this from the old invariant's membership of its length-$k$ prefix (`heavy_prefix_mem_goldreichLevinRetained_of_stageAccurate`). Third, every retained set has restricted Fourier weight greater than $\tau^2/4$, by the corresponding estimate-to-weight implication for retained sets (`restrictedFourierWeight_gt_quarter_of_mem_goldreichLevinRetained_of_stageAccurate`). These are precisely the three required clauses at stage $k+1$.

**Key facts.** `FABL.goldreichLevinCandidates_subset_prefixCoordinates_succ`, `FABL.heavy_prefix_mem_goldreichLevinRetained_of_stageAccurate`, `FABL.restrictedFourierWeight_gt_quarter_of_mem_goldreichLevinRetained_of_stageAccurate`.
