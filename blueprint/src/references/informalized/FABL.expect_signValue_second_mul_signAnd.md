<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.expect_signValue_second_mul_signAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-Sign Conjunction Expectation

**Claim.** For independent uniform signs $a,b$, if their conjunction is $-1$ exactly when both are $-1$ and is $1$ otherwise, then the mean of $b$ times the conjunction is $1/2$.

**Proof.** Evaluate over the four equally likely pairs $(a,b)$. For $(-1,-1)$, $b$ and the conjunction are both $-1$, so their product is $1$. For $(-1,1)$ and $(1,1)$ the product is also $1$, while for $(1,-1)$ the conjunction is $1$ and the product is $-1$. The four values therefore sum to $2$, and their uniform mean is $2/4=1/2$.
