<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.spaceUsed_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Space Use

**Claim.** If $t\le t'$, then the total number of distinct work-tape cells visited through step $t$ is at most the number visited through step $t'$.

**Proof.** Fix a work tape. Since $t\le t'$, every time index from $0$ through $t$ also lies between $0$ and $t'$. Consequently every head position visited on that tape by time $t$ is among those visited by time $t'$, so the earlier visited-position set is contained in the later one. The cardinality of a finite set cannot decrease under inclusion. Summing this inequality over all tapes gives the result. The containment of visited-position sets is the fact that extending the time horizon preserves all earlier visits (`Turing.MultiTapeTM.visitedByTapeHead_mono`).

**Key facts.** `Turing.MultiTapeTM.visitedByTapeHead_mono`.
