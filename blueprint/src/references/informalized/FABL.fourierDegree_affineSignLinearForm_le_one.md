<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/IntegralThresholdRepresentations.lean :: FABL.fourierDegree_affineSignLinearForm_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of an affine sign linear form

**Claim.** The function $x\mapsto a_0+\sum_i a_i\,\mathrm{signValue}(x_i)$ on the Boolean cube has Fourier degree at most $1$.

**Proof.** Write the function as $p(x)=a_0\chi_{\varnothing}(x)+\sum_i a_i\chi_{\{i\}}(x)$, where $\chi_R$ denotes the monomial indexed by $R$. To show degree at most $1$, it suffices to show every Fourier coefficient indexed by a set $S$ with $|S|>1$ vanishes (`FABL.fourierDegree_le_iff`). By linearity of expectation, that coefficient is $a_0$ times the expected product of the empty-set monomial with $\chi_S$, plus the sum over $i$ of $a_i$ times the expected product of $\chi_{\{i\}}$ with $\chi_S$. Distinct Boolean monomials are orthogonal: their expected product is $1$ when their index sets agree and $0$ otherwise (`FABL.expect_monomial_mul`). Since $|S|>1$, it is neither empty nor a singleton, so every term is zero. Hence all coefficients above degree one vanish, proving the bound.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.expect_monomial_mul`.
