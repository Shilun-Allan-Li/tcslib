<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteFourierBasis.productInfluence_le_one_of_hasSignRange -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence bound for sign-valued functions

**Claim.** If $f$ takes only the values $-1$ and $1$, then its influence at every coordinate is at most $1$.

**Proof.** The Fourier formula for the influence at coordinate $i$ expresses it as the sum of squared Fourier coefficients over multi-indices whose $i$th entry is not the constant index. Since every squared coefficient is nonnegative, this restricted sum is at most the sum over all multi-indices. Parseval's identity identifies the full sum with the second moment of $f$. Because $f(x)^2=1$ at every point, its expectation, and hence that second moment, is $1$.

**Key facts.** `FABL.FiniteFourierBasis.productInfluence_eq_sum_sq_fourierCoeff`, `FABL.FiniteFourierBasis.parseval`, `FABL.pmfExpectation_sq_eq_one_of_hasSignRange`.
