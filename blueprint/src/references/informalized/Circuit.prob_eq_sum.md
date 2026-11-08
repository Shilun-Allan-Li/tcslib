<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/polylogIndep.lean :: Circuit.prob_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability as a Weighted Sum

**Claim.** For a circuit $C$ and a probability mass function $\mu$ on Boolean assignments, its probability under $\mu$ is the sum over assignments of the indicator that $C$ evaluates to true, weighted by the mass of each assignment.

**Proof.** Unfold the definition of the circuit probability, so each summand is $\mu(x)$ when $C(x)$ is true and $0$ otherwise. For each assignment, if $C(x)$ is true then multiplying its mass by the indicator $1$ leaves it unchanged; if $C(x)$ is false then the indicator is $0$, so the product is $0$. Thus the two finite sums have equal terms at every assignment and hence are equal.
