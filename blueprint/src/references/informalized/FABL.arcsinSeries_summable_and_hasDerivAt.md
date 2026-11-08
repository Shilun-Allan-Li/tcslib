<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.arcsinSeries_summable_and_hasDerivAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arcsine Series and Its Derivative

**Claim.** For each integer $j\ge 0$, let $c_j=\binom{2j}{j}/(2^{2j}(2j+1))$. If $z\in\mathbb R$ satisfies $|z|<1$, then the series $\sum_{j=0}^{\infty}c_jz^{2j+1}$ converges, and the function $y\mapsto\sum_{j=0}^{\infty}c_jy^{2j+1}$ is differentiable at $z$ with derivative $(1-z^2)^{-1/2}$.

**Proof.** Choose $r=(|z|+1)/2$. The hypothesis $|z|<1$ ensures $0<r<1$ and $z\in(-r,r)$. The geometric series with terms $r^{2j}$ converges. On the interval $(-r,r)$, the derivative of the $j$th term, $c_j y^{2j+1}$, is the central binomial ratio $\binom{2j}{j}/2^{2j}$ times $y^{2j}$. The ratio is nonnegative and at most $1$ (`centralBinomialRatio_nonneg`, `centralBinomialRatio_le_one`), so the absolute value of this derivative is bounded by $r^{2j}$. Each original term vanishes at $y=0$, making its series summable there. The theorem on summability and termwise differentiation of a series on a connected open interval, applied with this geometric majorant, gives convergence at $z$ and identifies the derivative of the sum with the sum of the derivatives at $z$. By the binomial-series identity (`exercise5_18a`), that derivative series sums to $(1-z^2)^{-1/2}$. The derivative formula for each term used here is supplied by `hasDerivAt_arcsinSeriesTerm`.

**Key facts.** `FABL.centralBinomialRatio_nonneg`, `FABL.centralBinomialRatio_le_one`, `FABL.hasDerivAt_arcsinSeriesTerm`, `FABL.exercise5_18a`.
