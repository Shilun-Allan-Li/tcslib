<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.arcsinOddPowerCoefficient_mul_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing of Even-Index Coefficients

**Claim.** For every natural number $j$, the arcsine power-series coefficient indexed by $2j$ is zero.

**Proof.** The coefficient at index $2j$ is zero by the established even-index vanishing lemma ($\texttt{arcsinOddPowerCoefficient_two_mul}$). Since multiplication of natural numbers is commutative, $j\cdot2=2\cdot j$, so the same result gives the coefficient at index $j\cdot2$ as zero.

**Key facts.** `FABL.arcsinOddPowerCoefficient_two_mul`.
