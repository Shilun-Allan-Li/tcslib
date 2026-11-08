<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productStableInfluence_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of stable influence

**Claim.** Under the stated finite-basis hypotheses, the stable influence of any function at any coordinate is nonnegative for every $\rho\in(0,1]$.

**Proof.** The stable influence equals its stable-influence polynomial (`FiniteFourierBasis.productStableInfluence_eq_polynomial`). In that polynomial, each summand is a power of $\rho$ multiplied by a squared Fourier coefficient. Since $\rho>0$, the power is nonnegative, and a square is nonnegative; therefore each product and hence their finite sum is nonnegative.

**Key facts.** `FABL.FiniteFourierBasis.productStableInfluence_eq_polynomial`.
