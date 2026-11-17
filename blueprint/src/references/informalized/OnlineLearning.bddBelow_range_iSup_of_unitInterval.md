<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxNoRegret.lean :: OnlineLearning.bddBelow_range_iSup_of_unitInterval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for Suprema

**Claim.** If $\kappa$ is nonempty and every value $g(i,j)$ lies in $[0,1]$, then the range of the function $i\mapsto\sup_{j\in\kappa}g(i,j)$ is bounded below.

**Proof.** Use $0$ as a common lower bound. For each $i$, choose an element $j_0\in\kappa$, which exists by nonemptiness. The supremum over $j$ is at least $g(i,j_0)$, and $g(i,j_0)\ge 0$. Thus every value of the function lies above $0$. The upper bound $g(i,j)\le 1$ ensures the supremum is well-defined as a real supremum.

**Key facts.** `OnlineLearning.bddAbove_of_le_one`.
