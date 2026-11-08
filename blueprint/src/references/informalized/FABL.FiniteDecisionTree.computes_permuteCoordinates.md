<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.FiniteDecisionTree.computes_permuteCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate permutation preserves computation

**Claim.** If a Boolean function is invariant under a coordinate permutation and a decision tree computes it, then the tree with its queried coordinates permuted also computes it.

**Proof.** Fix an input $x$. The evaluation of the permuted tree at $x$ equals the evaluation of the original tree at the input whose $i$th coordinate is $x([0m\sigma(i))$ (`FABL.FiniteDecisionTree.eval_permuteCoordinates`). Since the original tree computes $f$, this is the value of $f$ at that permuted input. The assumed invariance of $f$ identifies that value with $f(x)$. Thus the two evaluation functions agree at every input, so the permuted tree computes $f$.

**Key facts.** `FABL.FiniteDecisionTree.eval_permuteCoordinates`.
