<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.existsUnique_biasedMinusProbabilityPolynomial_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unique parameter for a target value

**Claim.** For a monotone nonconstant Boolean function and any $\alpha\in(0,1)$, there is a unique $p\in(0,1)$ for which the biased-minus probability polynomial equals $\alpha$.

**Proof.** The polynomial has endpoint values $0$ and $1$ (`biasedMinusProbabilityPolynomial_endpoints`) and is continuous (`continuous_biasedMinusProbabilityPolynomial`). Since $\alpha$ lies strictly between those endpoint values, the intermediate value theorem supplies some $p\in[0,1]$ at which the polynomial equals $\alpha$. This point cannot be $0$ or $1$, because the endpoint values are respectively $0$ and $1$ while $0<\alpha<1$. Hence $p\in(0,1)$. If another $q\in(0,1)$ has the same value, both points lie in $[0,1]$, where the polynomial is strictly increasing (`strictMonoOn_biasedMinusProbabilityPolynomial`); strict monotonicity makes it injective, so $q=p$.

**Key facts.** `FABL.biasedMinusProbabilityPolynomial_endpoints`, `FABL.continuous_biasedMinusProbabilityPolynomial`, `FABL.strictMonoOn_biasedMinusProbabilityPolynomial`.

**Caveat.** The formal theorem proves existence and uniqueness for each target $\alpha\in(0,1)$; it does not itself assert the critical-probability characterization stated in the informal context.
