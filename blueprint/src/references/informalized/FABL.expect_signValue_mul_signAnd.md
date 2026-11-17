<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.expect_signValue_mul_signAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlation with a Sign Conjunction

**Claim.** For independent uniform signs $a,b$, the mean of the product of $a$ and their conjunction is $1/2$.

**Proof.** Evaluate the iterated uniform mean by summing over the four pairs $(a,b)\in\{-1,1\}^2$ and dividing by $4$. The conjunction is $-1$ only for $a=b=-1$, and is $1$ for the other three pairs. The products of $a$ with the conjunction, in the order $(-1,-1),(-1,1),(1,-1),(1,1)$, are $1,-1,1,1$. Their sum is $2$, so the mean is $2/4=1/2$.
