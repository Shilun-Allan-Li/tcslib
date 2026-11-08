<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedKKL.lean :: FABL.exercise9_30_asymptotic_bound_of_large -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic maximum-influence lower bound

**Claim.** Under the stated assumptions on $n$, every Boolean function has maximum coordinate influence at least $\tfrac12\operatorname{Var}(f)(\log n)/n\,(1-(\log n)^{-1/2})$.

**Proof.** Write $V$ for the variance, $I$ for total influence, $K=I/V$, $M$ for maximum influence, and $L=\log n$. If $V=0$, nonnegativity of maximum influence gives the result immediately. Otherwise $0<V\le1$, and variance is at most total influence (`variance_le_totalInfluence`), so $K\ge1$. Put $R=K^{1/3}$. The error term is $L^{-1/2}$; the assumptions ensure it lies between zero and one. Split into two cases. If $(L-\sqrt L)/2\le K$, then total influence is at most $nM$ (`totalInfluence_le_natCast_mul_maximumInfluence`), while $I=KV$. Combining these inequalities with $L(1-L^{-1/2})=L-\sqrt L$ proves the desired bound. Otherwise $K<(L-\sqrt L)/2$. Since $K\ge1$, logarithmic estimates give $2R\log K\le24L^{5/12}$; the assumed power bound makes this at most $\sqrt L/4$. Also $R\le\sqrt L$, so $2R\log K+R/4\le\sqrt L/2$. The refined influence inequality (`exercise9_30_refined`) bounds $M$ below by an exponential expression involving $K$ and $R$. Rewriting its power term as an exponential and using the preceding estimate yields $\exp(-L+\sqrt L/2)\le M$. Since $\exp(L)=n$, this is $\exp(\sqrt L/2)/n\le M$, and the remaining hypothesis on $n$ implies $L/(2n)\le M$. Finally, $V\le1$ and $0\le1-L^{-1/2}$ show that the target expression is at most $L/(2n)$, completing this case as well.

**Key facts.** `FABL.variance_eq_four_mul_probabilities`, `FABL.variance_le_totalInfluence`, `FABL.totalInfluence_le_natCast_mul_maximumInfluence`, `FABL.exercise9_30_refined`, `FABL.maximumInfluence_nonneg`.
