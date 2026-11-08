<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.integral_eq_pmf_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral as a finite weighted sum

**Claim.** On a finite probability space, the integral of any real-valued function is the sum of its values weighted by the real masses of the points.

**Proof.** For a finite measurable space, integration of a real-valued function is the finite sum of its values multiplied by the measures of the corresponding singleton sets. The canonical measure associated to the probability mass function assigns each singleton its PMF mass. Replacing those singleton measures by their real PMF values gives the claimed weighted-sum formula.
