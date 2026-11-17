<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.hermiteCoeff_finset_sum_hermiteFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite coefficients of finite sums

**Claim.** The Hermite coefficient at $\beta$ of a finite linear combination of Hermite functions is the sum of the coefficients $c_i$ for which $a_i=\beta$, with all other terms contributing zero.

**Proof.** Expand the product of the finite sum with the Hermite function at $\beta$ into the corresponding finite sum of products. Each term is integrable: Hermite functions belong to $L^2$ (\texttt{hermiteFunction\_memLp\_two}), so the product of two such functions is integrable, and multiplication by the constant $c_i$ preserves integrability. Linearity of integration over a finite sum and extraction of the constant reduce the coefficient to a sum of pairwise Hermite integrals. Orthogonality gives $1$ when $a_i=\beta$ and $0$ otherwise (\texttt{integral\_hermiteFunction\_mul}); hence precisely the stated coefficients remain.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteFunction_memLp_two`, `BooleanAnalysis.GaussianSpace.integral_hermiteFunction_mul`.
