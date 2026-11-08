<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.expect_recursiveMajorityThree_disagreement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Majority Disagreement

**Claim.** For every depth, two independent uniform inputs to recursive three-ary majority have different outputs with probability one half.

**Proof.** Let $f(x)$ be the real sign value of recursive three-ary majority on input $x$. Because the output is a sign, the indicator that the two outputs differ equals $(1-f(x)f(y))/2$. Thus the desired expectation is one half of the expectation of $1-f(x)f(y)$. Linearity makes this $1/2$ times $1$ minus one half times the expectation of the product. Independence separates that product expectation into $(mathbb E f(x))(mathbb E f(y))$. The mean-zero theorem for recursive three-ary majority says each factor is zero, so the disagreement expectation is $1/2$.

**Key facts.** `FABL.expect_div_const`, `FABL.expect_pair_mul_separate`, `FABL.expect_recursiveMajorityThree_toReal_eq_zero`.
