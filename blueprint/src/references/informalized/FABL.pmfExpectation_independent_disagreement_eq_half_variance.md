<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.pmfExpectation_independent_disagreement_eq_half_variance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Disagreement and Variance

**Claim.** If $f$ takes values in $\{-1,1\}$ and $X,Y$ are independent samples from $\pi$, then the probability that $f(X)\ne f(Y)$ equals one half of the variance of $f(X)$.

**Proof.** Write $m=\mathbb{E}_{\pi}f$. For two sign values, the disagreement indicator is $(1-f(x)f(y))/2$: the product is $1$ when the values agree and $-1$ when they differ. Averaging first over $y$ therefore gives $(1-f(x)m)/2$, using linearity of expectation, the expectation of a constant, and the rule for taking a scalar multiple through expectation (\texttt{FABL.pmfExpectation\_add\_fun}, \texttt{FABL.pmfExpectation\_const}, and \texttt{FABL.pmfExpectation\_smul\_fun}). Averaging this expression over $x$ gives $(1-m^2)/2$ by the same expectation rules. Finally, because $f(x)^2=1$ at every point, expanding $(f(x)-m)^2$ and taking expectations gives $\mathbb{E}_{\pi}[(f-m)^2]=1-2m^2+m^2=1-m^2$; the identity $\mathbb{E}_{\pi}[f^2]=1$ is supplied by the sign-range square expectation lemma (\texttt{FABL.pmfExpectation\_sq\_eq\_one\_of\_hasSignRange}). Combining these equalities proves the result.

**Key facts.** `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_smul_fun`, `FABL.pmfExpectation_sq_eq_one_of_hasSignRange`.
