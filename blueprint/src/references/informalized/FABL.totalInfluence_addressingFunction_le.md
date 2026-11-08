<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.totalInfluence_addressingFunction_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addressing Function Influence Bound

**Claim.** For every natural number $m$, the total influence of the addressing function on sign vectors of dimension $m+2^m$ is at most $m+1$.

**Proof.** The total influence of a Boolean function's real-valued form equals the expected sensitivity of the Boolean function (`FABL.totalInfluence_toReal_eq_expect_sensitivity`). At every input, the addressing function's sensitivity is at most $m+1$ (`FABL.sensitivity_addressingFunction_le`). Taking expectations preserves this pointwise inequality, and the expectation of the constant $m+1$ is $m+1$.

**Key facts.** `FABL.totalInfluence_toReal_eq_expect_sensitivity`, `FABL.sensitivity_addressingFunction_le`.
