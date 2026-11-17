<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.sequentialOrTree_averageCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost on All Coordinates

**Claim.** For $n$ independent signs, each equal to $-1$ with probability $p$ and $1$ with probability $1-p$, the sequential OR tree's expected query count is $\sum_{k=0}^{n-1}(1-p)^k$.

**Proof.** The sequential OR tree on all $n$ coordinates is the auxiliary sequential tree for the full coordinate set. The auxiliary and deterministic average-cost definitions agree for a tree on the full coordinate set (\texttt{FiniteDecisionTree.auxiliaryAverageCost\_complete}). Applying the auxiliary average-cost formula to that full set gives $\sum_{k=0}^{|\mathrm{Fin}(n)|-1}(1-p)^k$. Since the full coordinate set has size $n$, this is the asserted sum.

**Key facts.** `FABL.FiniteDecisionTree.auxiliaryAverageCost_complete`, `FABL.sequentialOrTreeAux_averageCost`.
