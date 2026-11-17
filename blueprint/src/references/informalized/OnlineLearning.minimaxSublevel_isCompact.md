<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.minimaxSublevel_isCompact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compactness of the Minimax Sublevel Set

**Claim.** If $X$ is compact and $x\mapsto f(x,y)$ is continuous on $X$, then the minimax sublevel set is compact.

**Proof.** The minimax sublevel set is closed by the closedness result for minimax sublevel sets (OnlineLearning.minimaxSublevel_isClosed), applied using that compact sets are closed. It is also contained in $X$ by the defining intersection (OnlineLearning.minimaxSublevel_subset). A closed subset of a compact set is compact, so the sublevel set is compact.

**Key facts.** `OnlineLearning.minimaxSublevel_isClosed`, `OnlineLearning.minimaxSublevel_subset`.
