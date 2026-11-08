<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.goldreichLevinRunUpTo_prefixes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Support of Run Families

**Claim.** For every $k\le n$, if the run through stage $k$ returns an active family $A$, then every member of $A$ is contained in the first $k$ coordinates.

**Proof.** Induct on the stage. At stage zero the run returns only the empty set, which is contained in the empty prefix. For stage $k+1$, inspect the run through stage $k$. If that run failed, the successor run also fails, contrary to the assumed returned value. Otherwise it returns a family supported on the first $k$ coordinates by induction. Every member retained at the next stage is a candidate formed from this family, and candidates are supported on the first $k+1$ coordinates (`goldreichLevinCandidates_subset_prefixCoordinates_succ`). The returned family is exactly the retained family: if the cap condition fails refinement returns no result, which is impossible here; if it holds, refinement returns the retained family. This proves the support claim.

**Key facts.** `FABL.goldreichLevinCandidates_subset_prefixCoordinates_succ`.
