<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.expect_signValue_mul_signValue_mul_signAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triple Moment with a Sign Conjunction

**Claim.** For independent uniform signs $a,b$, the mean of the product of $a$, $b$, and their conjunction is $-1/2$.

**Proof.** Sum the integrand over the four equally likely pairs of signs. At $(-1,-1)$ the conjunction is $-1$, so the product is $-1$; at $(-1,1)$ and $(1,-1)$ the conjunction is $1$, so the product is $-1$ in each case; at $(1,1)$ the product is $1$. The four values sum to $-2$. Dividing by $4$ gives $-1/2$.
