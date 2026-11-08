<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.RandomizedDecisionTree.inputCost_nandAllTrue_eq_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NAND Cost at the All-True Input

**Claim.** Every zero-error randomized decision tree computing NAND on two sign inputs has expected query count exactly $2$ at the input where both coordinates equal $-1$.

**Proof.** For each seed, the selected deterministic tree computes NAND. The deterministic lower-level fact that every such tree queries exactly two coordinates at the all-$-1$ input (`FiniteDecisionTree.queryCount_nandAllTrue_eq_two`) therefore makes the query count equal to $2$ for every seed. The expectation of this constant query count under the seed distribution is $2$ (`pmfExpectation_const`).

**Key facts.** `FABL.FiniteDecisionTree.queryCount_nandAllTrue_eq_two`, `FABL.pmfExpectation_const`.
