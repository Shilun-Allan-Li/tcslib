<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RobustEdgeIsoperimetry.lean :: FABL.positive_dimension_of_isBalanced -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Dimension of a Balanced Sign Function

**Claim.** If the uniform mean of a sign-valued function on the $n$-dimensional Boolean cube is zero, then $n>0$.

**Proof.** Suppose instead that $n=0$. The zero-dimensional cube has only one point, so the function is constant there, with value equal to either $1$ or $-1$. Its uniform mean is therefore that same value, which cannot be zero. This contradicts balance, and hence $n>0$.
