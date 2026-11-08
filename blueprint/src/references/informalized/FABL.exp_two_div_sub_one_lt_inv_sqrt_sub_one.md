<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractivityExercises.lean :: FABL.exp_two_div_sub_one_lt_inv_sqrt_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential reciprocal square-root bound

**Claim.** For every real $p$ with $1<p<2$, one has $\exp(2/p-1)<1/\sqrt{p-1}$.

**Proof.** Set $x=p-1$, so $0<x<1$ and $2/p-1=(1-x)/(1+x)$. The logarithmic inequality $2(1-x)/(1+x)<-\log x$ (by `two_mul_one_sub_div_one_add_lt_neg_log`) gives $(1-x)/(1+x)<-\tfrac12\log x$. Since $x>0$, the logarithm laws identify the right-hand side with $\log(1/\sqrt{x})$. The exponential is strictly increasing, so exponentiating yields $\exp((1-x)/(1+x))<1/\sqrt{x}$. Substituting the expressions for $x$ and the exponent proves the result.

**Key facts.** `FABL.two_mul_one_sub_div_one_add_lt_neg_log`.
