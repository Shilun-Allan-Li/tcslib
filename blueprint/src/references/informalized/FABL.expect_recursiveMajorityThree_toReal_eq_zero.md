<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.expect_recursiveMajorityThree_toReal_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of Recursive Majority

**Claim.** At every depth, the real sign value of recursive three-ary majority has mean zero under the uniform input distribution.

**Proof.** The function taking an input to the real sign value of its recursive-majority output is odd: negating every input sign negates the output, and therefore negates its real sign value. The oddness of recursive majority is supplied by the lemma on oddness of recursive majority (FABL.recursiveMajority_odd). On a finite sign cube, negation permutes the inputs, so the sum of an odd function over the cube is its own negative and hence is zero. Dividing that sum by the cube’s cardinality gives the zero expectation.

**Key facts.** `FABL.recursiveMajority_odd`.
