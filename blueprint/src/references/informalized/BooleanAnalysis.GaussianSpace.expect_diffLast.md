<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Cube.lean :: BooleanAnalysis.GaussianSpace.expect_diffLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of the last-coordinate half-difference

**Claim.** The uniform expectation of the last-coordinate half-difference is half the difference between the expectations of the two restrictions.

**Proof.** By definition, the half-difference at each point is $(f_0(x)-f_1(x))/2$, and expectation is a constant weight times the sum over all points of the cube. Distributing the finite sum over subtraction and factoring out $1/2$ gives $\mathbb E[d]=(\mathbb E[f_0]-\mathbb E[f_1])/2$.
