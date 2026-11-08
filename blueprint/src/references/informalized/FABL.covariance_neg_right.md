<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityCharacterizations.lean :: FABL.covariance_neg_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negating the Second Covariance Argument

**Claim.** For real-valued functions $f,h$ on the sign cube, $\operatorname{Cov}(f,-h)=-\operatorname{Cov}(f,h)$.

**Proof.** The mean of $-h$ is $-\operatorname{mean}(h)$ by linearity of expectation. Substituting this into the definition of covariance, the second centered factor becomes $(-h)(x)-(-\operatorname{mean}(h))=-(h(x)-\operatorname{mean}(h))$. Thus the integrand is the negative of the integrand defining $\operatorname{Cov}(f,h)$. Linearity of expectation pulls this minus sign outside, proving the identity.
