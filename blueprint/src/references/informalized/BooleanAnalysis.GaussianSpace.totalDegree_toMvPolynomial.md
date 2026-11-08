<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Degree.lean :: BooleanAnalysis.GaussianSpace.totalDegree_toMvPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of an embedded univariate polynomial

**Claim.** When a real polynomial $p$ is regarded as a multivariate polynomial in a single variable indexed by $i$, its total degree equals its natural degree.

**Proof.** Use Horner recursion on $p$. The zero polynomial has total degree and natural degree zero. In the constant-addition step, write the polynomial as $q+a$. Its natural degree is the degree of $q$ when that degree is positive. If $q$ instead has degree zero, both summands have total degree zero, so their sum has total degree at most zero and hence degree zero. If $q$ has positive degree, adding a constant cannot change its leading degree: the multivariate total degree of the sum equals that of the higher-degree summand. In the multiplication-by-variable step, the embedded polynomial is the product of the embedding of $q$ and the variable indexed by $i$. Both factors are nonzero, so total degrees add; the induction hypothesis and the univariate degree formula for multiplication by a variable give the result.
