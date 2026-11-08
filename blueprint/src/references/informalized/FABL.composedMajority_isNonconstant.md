<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.composedMajority_isNonconstant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonconstancy of Composed Majority

**Claim.** For every $m\ge 0$, the composed majority on the sign cube of dimension $2+(2m+1)$ is nonconstant.

**Proof.** Evaluate the function at the all-$-1$ input and at the all-$+1$ input. The inner majority has positive arity $2m+1$, so unanimity of majority (`majority_unanimous`) makes its outputs $-1$ and $+1$, respectively. In each case all three inputs to the outer three-coordinate majority agree, so applying the same unanimity fact at arity $3$ shows that the composed outputs are $-1$ and $+1$. These outputs differ, proving nonconstancy.

**Key facts.** `FABL.majority_unanimous`.
