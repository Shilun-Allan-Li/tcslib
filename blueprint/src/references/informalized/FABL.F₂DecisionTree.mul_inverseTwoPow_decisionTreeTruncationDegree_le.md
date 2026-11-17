<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.mul_inverseTwoPow_decisionTreeTruncationDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision Tree Truncation Degree Bound

**Claim.** For positive $s$ and $\varepsilon$, if $d=\left\lceil\log_2(s/\varepsilon)\right\rceil$, then $s\,2^{-d}\leq\varepsilon$.

**Proof.** Set $r=s/\varepsilon$, which is positive. By the defining property of the ceiling, $\log_2 r\leq d$. Since the base $2$ is greater than $1$, exponentiating gives $r\leq 2^d$. Multiplying by the positive number $\varepsilon$ yields $s\leq\varepsilon 2^d$. As $2^d>0$, divide by it to obtain $s2^{-d}\leq\varepsilon$.
