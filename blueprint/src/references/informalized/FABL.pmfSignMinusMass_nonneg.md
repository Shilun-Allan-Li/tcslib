<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.pmfSignMinusMass_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Minus-One Mass

**Claim.** For a finite set, a probability mass function $\pi$, and $f:\Omega\to\mathbb{R}$, the mass assigned to points where $f(x)=-1$ is nonnegative.

**Proof.** The minus-one mass is the expectation of the indicator that $f(x)=-1$. This indicator is nonnegative at every point, so its expectation is nonnegative by nonnegativity of PMF expectations (\texttt{FABL.pmfExpectation_nonneg}).

**Key facts.** `FABL.pmfExpectation_nonneg`.
