<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.biasedMinusProbabilityPolynomial_le_epsilon_refined -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Refined small-parameter bound

**Claim.** Under the stated hypotheses, if $p\le 4(\tau/(1+\tau))^{1-\tau}\epsilon^{1+\tau}p_c$, then the biased minus-probability polynomial at $p$ is at most $\epsilon$.

**Proof.** 1. Put $r=\tau/(1+\tau)$ and $p_a=(2r)^2p_c$. The parameter-range lemma gives $0<r<1/2$; hence $0<p_a\le p_c<1$. The critical square-scale estimate, applied with parameter $r$ and $p_a\le(2r)^2p_c$, gives that the polynomial at $p_a$ is at most $r$. If $p=0$, the endpoint value is zero, so the result follows from $\epsilon>0$.

2. Suppose $p>0$. Taking logarithms of the assumed cutoff and comparing with $p_a$ gives $\log p\le\log p_a$: explicitly, the logarithm of the cutoff minus $\log p_a$ is $(1+\tau)(\log\epsilon-\log r)\le0$, since $\epsilon<r$. Thus $0<p\le p_a$. The refined power bound, applied using the estimate at $p_a$, now gives $F(p)\le r(p/p_a)^{1-r}$, where $F$ denotes the polynomial. The polynomial is positive at interior parameters (biasedMinusProbabilityPolynomial_mem_Ioo), so logarithms may be taken.

3. The identity $1-r=1/(1+\tau)$ and the cutoff assumption imply
$\log r+(1-r)(\log p-\log p_a)\le\log\epsilon$.
Indeed, replace $\log p$ by its upper bound $\log$ of the cutoff and use the logarithmic comparison from the previous step. Taking logarithms in the refined power bound therefore gives $\log F(p)\le\log\epsilon$. Since both quantities are positive, exponentiating proves $F(p)\le\epsilon$.

**Key facts.** `FABL.refinedThresholdLevel_mem_Ioo`, `FABL.biasedMinusProbabilityPolynomial_le_epsilon_of_le_sq_mul_critical`, `FABL.biasedMinusProbabilityPolynomial_endpoints`, `FABL.biasedMinusProbabilityPolynomial_le_refined_rpow`, `FABL.one_sub_refinedThresholdLevel`, `FABL.biasedMinusProbabilityPolynomial_mem_Ioo`.
