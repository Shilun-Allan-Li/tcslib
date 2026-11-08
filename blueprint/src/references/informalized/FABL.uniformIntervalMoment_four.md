<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ContinuousReasonableness.lean :: FABL.uniformIntervalMoment_four -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth uniform interval moment

**Claim.** The fourth moment of the uniform distribution on $[-1,1]$, defined by $\frac12\int_{-1}^{1}x^4\,dx$, is $\frac15$.

**Proof.** By the power rule for integration, $\int_{-1}^{1}x^4\,dx=[x^5/5]_{-1}^{1}=1/5-(-1/5)=2/5$. Multiplying by the density factor $1/2$ gives $1/5$.
