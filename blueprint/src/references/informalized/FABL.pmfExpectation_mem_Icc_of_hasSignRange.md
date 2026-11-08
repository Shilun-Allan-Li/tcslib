<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.pmfExpectation_mem_Icc_of_hasSignRange -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for sign-valued expectations

**Claim.** If $f$ takes only the values $-1$ and $1$, then its expectation under $\pi$ lies in $[-1,1]$.

**Proof.** For every outcome, $-1\le f(x)\le 1$. Monotonicity of expectation transfers each pointwise inequality to expectations (`FABL.pmfExpectation_mono`). The expectation of a constant is that constant (`FABL.pmfExpectation_const`), so the two resulting bounds are $-1\le \mathbb{E}_{\pi}[f]\le 1$.

**Key facts.** `FABL.pmfExpectation_const`, `FABL.pmfExpectation_mono`.
