<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.innerProductModTwoSupportDensity_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise Formula for Support Density

**Claim.** For positive $m$ and $z\in\mathbb{F}_2^{2m}$, the support density at $z$ is the reciprocal of the uniform probability of the inner-product-one event, multiplied by the indicator of that event at $z$.

**Proof.** Replace the support density by its pointwise value using the formula for evaluating a subset density (\texttt{subsetDensity_apply}). By definition, that value is the reciprocal of the event's uniform probability times the indicator of the support. The indicator of this particular support is exactly the real embedding of the inner-product bit (\texttt{setIndicator_innerProductModTwoOneSet}), giving the claimed expression.

**Key facts.** `FABL.subsetDensity_apply`, `FABL.setIndicator_innerProductModTwoOneSet`.
