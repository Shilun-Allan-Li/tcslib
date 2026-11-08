<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.continuous_stableInfluencePolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the stable influence polynomial

**Claim.** Under the stated finite probability-space and orthonormal-basis hypotheses, for every function $f$ and coordinate $i$, the stable influence polynomial is continuous in $\rho$.

**Proof.** The stable influence is a finite sum over multi-indices whose $i$th entry is nonzero. For each such index, its summand is a fixed squared Fourier coefficient multiplied by $\rho$ raised to a fixed natural-number exponent. Each summand is therefore a polynomial in $\rho$ and is continuous. A finite sum of these continuous functions is continuous.
