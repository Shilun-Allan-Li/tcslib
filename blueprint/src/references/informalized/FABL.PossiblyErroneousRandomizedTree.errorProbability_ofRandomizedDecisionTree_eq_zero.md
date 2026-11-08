<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.PossiblyErroneousRandomizedTree.errorProbability_ofRandomizedDecisionTree_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Error Probability

**Claim.** If every seed of a randomized decision tree computes the same function correctly, then its error probability under any input law is zero.

**Proof.** Fix a seed. Correctness says that the tree's evaluation agrees with the target function on every input, so the indicator of an error is identically zero. The expectation of this constant-zero function under the input law is zero. Thus the error as a function of the seed is also identically zero, and its expectation under the seed law is zero as well; here we use that the expectation of a constant function equals that constant (\texttt{pmfExpectation\_const}).

**Key facts.** `FABL.pmfExpectation_const`.
