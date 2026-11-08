<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/polylogIndep.lean :: Circuit.prob_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability Is Nonnegative

**Claim.** For a circuit $C$ and a probability mass function $\mu$ on Boolean assignments, the probability that $C$ evaluates to true under $\mu$ is nonnegative.

**Proof.** Each summand defining the probability is either $(\mu(x)).\mathrm{toReal}$ or $0$. Both are nonnegative, because the real-valued mass of an assignment is nonnegative. A finite sum of nonnegative terms is nonnegative, so the circuit probability is nonnegative.
