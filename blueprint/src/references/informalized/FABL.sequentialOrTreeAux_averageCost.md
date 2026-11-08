<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.sequentialOrTreeAux_averageCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost of the Sequential OR Tree

**Claim.** For a finite coordinate set $A$ and independent signs with probability $p$ of being $-1$, the sequential OR tree's expected query count is $\sum_{k=0}^{|A|-1}(1-p)^k$.

**Proof.** Proceed by strong induction on the size of $A$. If $A$ is empty, the tree is a leaf, so its query cost is zero, matching the empty sum. Otherwise, let $i$ be the least element of $A$. The tree queries $i$ first. If its value is $-1$, it stops at cost one; if its value is $1$, it incurs one query plus the cost of the tree on $A\setminus\{i\}$. The latter subtree's query trace depends only on coordinates in $A\setminus\{i\}$, so changing coordinate $i$ does not affect its cost. The product-measure diagonal-section formula therefore reduces the expected cost to the expectation over the value at $i$ of these two branch costs (\texttt{FiniteDecisionTree.productMean\_diagonal\_section}). Under the biased sign law, these values occur with probabilities $p$ and $1-p$ (\texttt{pmfExpectation\_biasedSignPMF}); hence the expectation is $p\cdot 1+(1-p)(1+C_{|A|-1})$, where $C_{|A|-1}$ is the expected cost for the smaller set. By induction this is $1+(1-p)\sum_{k=0}^{|A|-2}(1-p)^k$, which equals the desired sum by the recurrence for the geometric cost (\texttt{orAverageQueryCost\_succ}).

**Key facts.** `FABL.FiniteDecisionTree.productMean_diagonal_section`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_biasedSignPMF`, `FABL.orAverageQueryCost_succ`.
