<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.expect_signValue_mul_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Moment with a Power

**Claim.** For every nonnegative integer $k$ and real number $c$, the uniform mean of $b(b^k c)$ over signs $b$ is $c$ when $k$ is odd and $0$ when $k$ is even.

**Proof.** For each sign $b$, regroup the integrand as $c b^{k+1}$, using $b\cdot b^k=b^{k+1}$. Linearity of the uniform mean then gives $c$ times the mean of $b^{k+1}$. The sign moment formula ( `expect_signValue_pow_succ`) says that this latter mean is $1$ for odd $k$ and $0$ for even $k$. Multiplying by $c$ gives the two claimed cases.

**Key facts.** `FABL.expect_signValue_pow_succ`.
