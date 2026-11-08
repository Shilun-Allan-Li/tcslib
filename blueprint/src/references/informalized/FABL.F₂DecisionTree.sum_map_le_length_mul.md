<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.sum_map_le_length_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Bound for List Sums

**Claim.** If every weight attached to an element occurring in a finite list is at most $B$, then the sum of the weights is at most the list length times $B$.

**Proof.** Induct on the list. For the empty list, both the sum and the length are zero. For a list with first element $i$ and tail $I$, the hypothesis bounds $w(i)$ by $B$ and also bounds every weight occurring in $I$ by $B. The induction hypothesis bounds the tail’s sum by $length(I)B$. Adding the first-element bound gives $w(i)+\sum_{j\in I}w(j)\le B+length(I)B=(1+length(I))B$, which is the desired bound for the whole list.
