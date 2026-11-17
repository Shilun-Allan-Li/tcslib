<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.tendsto_influenceModulusOfNoiseModulus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing influence modulus

**Claim.** If the noise modulus tends to zero as its parameter tends to zero from above, then the associated influence modulus tends to zero as the dimension tends to infinity.

**Proof.** First compose the assumed limit of $\varepsilon$ at zero with the fact `tendsto_inverseDimensionHalfNoiseParameter`: the parameter $1/n$ (for dimensions at least two) tends to zero from above. Hence the scaled values $\frac{2}{1-e^{-2}}\varepsilon(1/n)$ tend to zero as well, since the factor is constant. Taking the minimum of these values with the constant sequence $1$ still gives a sequence tending to zero. For all $n\ge2$, this minimum is exactly the influence modulus; the exceptional definition for $n<2$ affects only finitely many terms and therefore does not change the limit.

**Key facts.** `FABL.tendsto_inverseDimensionHalfNoiseParameter`.
