<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.completeTree_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical tree computes its function

**Claim.** For a nonempty alphabet, the canonical decision tree that queries the coordinates in order and places the value of a function at the corresponding leaf computes that function on every input.

**Proof.** To show the two functions are equal, fix an input $x$. The evaluation theorem for the auxiliary construction states that if a partial input already agrees with $x$ outside the coordinates still available, then evaluating the constructed subtree at $x$ returns $f(x)$ (`FABL.FiniteDecisionTree.eval_completeTreeAux`). Apply it to the initial partial input, which is constant at some alphabet element. Initially every coordinate is available, so the agreement condition outside that set is vacuous. The resulting equality gives the desired computation at $x$, and since $x$ was arbitrary, the functions agree everywhere.

**Key facts.** `FABL.FiniteDecisionTree.eval_completeTreeAux`.
