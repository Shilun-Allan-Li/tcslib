<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.sum_two_pow_pathLength_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Path-Length Powers

**Claim.** If every path in a finite list has length at most $k$, then the sum of $2^{length(p)}$ over the list is at most the list length times $2^k$.

**Proof.** Induct on the path list. The empty list satisfies the bound immediately. For a list with first path $p$ and a tail list, the hypothesis gives $length(p)\le k$ and gives the same bound for every path in the tail. Since powers of $2$ increase with their exponent, $2^{length(p)}\le 2^k$. By induction, the tail’s sum is at most its length times $2^k$. Adding these inequalities yields at most $(1+length(tail))2^k$, which is the length of the whole list times $2^k$.
