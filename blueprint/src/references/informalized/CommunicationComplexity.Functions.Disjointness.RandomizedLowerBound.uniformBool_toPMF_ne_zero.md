<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_toPMF_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full support of the uniform bit law

**Claim.** For either bit $b$, the uniform law on one bit assigns $b$ nonzero probability mass.

**Proof.** By the singleton-mass formula, the real mass of the singleton $\{b\}$ is $1/2$ (`uniformBool_singleton`). The mass assigned by the probability mass function is this same real mass, so its real value is $1/2$. If the mass were zero, its real value would be zero, contradicting $1/2\ne 0$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_singleton`.
