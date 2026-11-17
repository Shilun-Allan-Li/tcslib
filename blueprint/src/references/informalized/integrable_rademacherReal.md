<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: integrable_rademacherReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability under the Rademacher measure

**Claim.** Every real-valued function on $\mathbb R$ is integrable with respect to the Rademacher measure.

**Proof.** The Rademacher measure is the sum of the two half-scaled Dirac measures at $-1$ and $1$. Every real-valued function is integrable with respect to each of these scaled point masses, by the integrability-under-scaled-Dirac fact (integrable_smul_dirac). Integrability is preserved under addition of measures, so the function is integrable with respect to their sum.

**Key facts.** `integrable_smul_dirac`.
