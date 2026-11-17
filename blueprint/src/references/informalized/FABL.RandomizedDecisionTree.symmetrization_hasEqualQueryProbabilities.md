<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.RandomizedDecisionTree.symmetrization_hasEqualQueryProbabilities -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal query probabilities after symmetrization

**Claim.** If the symmetries of a Boolean function act transitively on coordinates, then its symmetrized randomized decision tree has equal query probability at every coordinate under any product input distribution with marginal \(\pi\).

**Proof.** Fix coordinates \(i\) and \(j\). The query probability of the symmetrized tree at a coordinate is the average, over the function’s symmetry group, of the original tree’s query probability at the coordinate carried back by that symmetry (`symmetrization_queryProbability`). Thus the two probabilities in question are averages of the original tree’s query probabilities over the same symmetry group, evaluated at the preimages of \(i\) and \(j\). Transitivity of the function’s symmetries implies these two averages agree (`symmetryAverage_queryProbability_eq`). Hence the symmetrized tree has equal query probabilities at \(i\) and \(j\), and the choice of coordinates was arbitrary.

**Key facts.** `FABL.RandomizedDecisionTree.symmetrization_queryProbability`, `FABL.RandomizedDecisionTree.symmetryAverage_queryProbability_eq`.
