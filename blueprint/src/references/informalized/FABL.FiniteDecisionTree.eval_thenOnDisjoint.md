<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.eval_thenOnDisjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of sequential decision trees

**Claim.** If $A$ and $B$ are disjoint, evaluating the tree formed by running $T$ and then the tree selected by its output gives the evaluation of that selected tree at the same input.

**Proof.** Proceed by induction on $T$. If $T$ is a leaf with value $a$, the constructed tree is the tree $K(a)$ weakened from available coordinates $B$ to $A\cup B$. Weakening the available set does not alter evaluation (\texttt{FABL.FiniteDecisionTree.eval\_weaken}), so the result is the evaluation of $K(a)$ at $x$, as required. If $T$ queries coordinate $i$, the constructed tree makes that same query and selects the child indexed by $x_i$. Its continuation is the sequential composition of that child with $K$, with the available set identified using disjointness of $A$ and $B$; changing the index along this equality preserves evaluation (\texttt{FABL.FiniteDecisionTree.eval\_castAvailable}). Applying the induction hypothesis to the selected child yields the evaluation of $K$ at the output of that child, which is precisely $K(T(x))$ evaluated at $x$.

**Key facts.** `FABL.FiniteDecisionTree.eval_weaken`, `FABL.FiniteDecisionTree.eval_castAvailable`.
