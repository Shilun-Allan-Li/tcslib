<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.polynomialThresholdInfluenceExponent_eq_one_sub_noiseExponent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relation between influence and noise exponents

**Claim.** For every natural number $k$, the polynomial threshold influence exponent is one minus the polynomial threshold noise exponent.

**Proof.** By definition, the influence exponent is $1-(2^k)^{-1}$, while the noise exponent is $(2^k)^{-1}$. Substituting the latter into one minus the noise exponent gives exactly the former.
