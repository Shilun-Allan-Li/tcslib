<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/KLDivergence.lean :: CommunicationComplexity.klDiv_eq_sum_llr_of_ac -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-space formula for relative entropy

**Claim.** On a finite measurable space with finite measures and $\mu\ll\nu$, the Kullback–Leibler divergence equals the nonnegative-real embedding of the finite sum of pointwise log-likelihood contributions, together with the difference of total masses.

**Proof.** Because the space is finite, the log-likelihood ratio is integrable with respect to the finite measure $\mu$. The absolute-continuity formula for Kullback–Leibler divergence therefore expresses the divergence as the nonnegative-real embedding of the integral of the log-likelihood ratio plus the total-mass correction. On a finite space, the integral is the sum over points: each term is the mass of the singleton $\{\omega\}$ under $\mu$, multiplied by the log-likelihood ratio at $\omega$. Substituting this finite-sum expression gives the stated formula.
