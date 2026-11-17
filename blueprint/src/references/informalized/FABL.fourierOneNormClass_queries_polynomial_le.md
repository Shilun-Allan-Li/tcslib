<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.fourierOneNormClass_queries_polynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Query Complexity

**Claim.** For a target Boolean function with Fourier one-norm at most $s$ and $0<\varepsilon\le1/2$, every outcome in the support of the query-mode Kushilevitz–Mansour procedure with the specified family-size parameter has query cost at most $2^{64}(n+1)^2(s+1)^{16}/\varepsilon^{18}$.

**Proof.** Write $M$ for the specified family-size bound. The query-cost estimate for the procedure bounds the cost by $2^{40}(n+1)^2(M+1)^8/\varepsilon^{10}$. The family-size estimate gives $M+1\le 6(s+1)^2/\varepsilon$; since both sides are nonnegative, raising to the eighth power and substituting yields an upper bound of $2^{40}6^8(n+1)^2(s+1)^{16}/\varepsilon^{18}$. Finally, $2^{40}6^8\le2^{64}$, giving the asserted estimate.

**Key facts.** `FABL.kushilevitzMansourProgramForBound_queries_polynomial_cast_le`, `FABL.fourierOneNormFamilySizeBound_add_one_cast_le`, `FABL.positiveLearningParameter_toReal_mem_Ioc`.
