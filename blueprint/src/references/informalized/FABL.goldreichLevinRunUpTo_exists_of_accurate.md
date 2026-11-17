<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.goldreichLevinRunUpTo_exists_of_accurate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of Every Run Prefix

**Claim.** For every $k\le n$, an accurate weight estimate ensures that running the refinement process through stage $k$ returns some active family.

**Proof.** Proceed by induction on $k$. At stage zero, the run returns the initial family consisting of the empty set. For the successor stage $k+1$, the induction hypothesis supplies a family returned at stage $k$. The run-prefix property says every member of that family lies in the first $k$ coordinates (`goldreichLevinRunUpTo_prefixes`). Each retained member is a candidate, so the candidate-support result places it in the first $k+1$ coordinates (`goldreichLevinCandidates_subset_prefixCoordinates_succ`). Accuracy of the global estimate ensures that each retained member has restricted Fourier weight at least $\tau^2/4$ (`restrictedFourierWeight_gt_quarter_of_mem_goldreichLevinRetained`). The counting bound for families supported on the stage prefix with this weight lower bound gives that the retained family has size at most the active cap (`card_prefixes_le_goldreichLevinActiveCap`). Consequently refinement succeeds and returns this retained family, completing the induction.

**Key facts.** `FABL.goldreichLevinRunUpTo_prefixes`, `FABL.goldreichLevinCandidates_subset_prefixCoordinates_succ`, `FABL.restrictedFourierWeight_gt_quarter_of_mem_goldreichLevinRetained`, `FABL.card_prefixes_le_goldreichLevinActiveCap`.
