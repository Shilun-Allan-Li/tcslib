<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.coeff_one_sub_X_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficients of a Binomial Power

**Claim.** The coefficient of $t^k$ in $(1-t)^z$ is $(-1)^k\binom{z}{k}$.

**Proof.** Rewrite $1-X$ as $1+(-X)$ and expand its $z$th power. The coefficient in degree $k$ receives a contribution only from the term selecting $k$ copies of $-X$; the number of such choices is $\binom{z}{k}$. The coefficient of $(-X)^k$ is $(-1)^k$ by the signed monomial coefficient formula (\texttt{coeff\_neg\_X\_pow}), so the resulting coefficient is $(-1)^k\binom{z}{k}$.

**Key facts.** `FABL.coeff_neg_X_pow`.
