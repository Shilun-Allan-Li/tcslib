<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.influence_extendedSignRestriction_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero influence outside restricted coordinates

**Claim.** For a function restricted by fixing all coordinates outside $J$, every coordinate $i\notin J$ has influence zero.

**Proof.** The discrete derivative of the extended restriction in coordinate $i$ is zero at every input, by the fact that changing a coordinate outside $J$ does not change the restricted function (\texttt{FABL.discreteDerivative_extendedSignRestriction_of_not_mem}). The influence is the expectation of the square of this derivative. Its integrand is therefore identically zero, so the expectation is zero.

**Key facts.** `FABL.discreteDerivative_extendedSignRestriction_of_not_mem`.
