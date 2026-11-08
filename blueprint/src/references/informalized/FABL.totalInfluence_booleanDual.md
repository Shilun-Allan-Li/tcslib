<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.totalInfluence_booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Influence Under Duality

**Claim.** For every Boolean function on sign vectors of dimension $n$, its Boolean dual has the same total influence as the original function.

**Proof.** Expand total influence as a sum over coordinates, and express each influence as the uniform average of the squared discrete derivative. For each coordinate and input, the squared derivative of the dual equals the squared derivative of the original function evaluated at the coordinatewise negation of that input (`FABL.sq_discreteDerivative_booleanDual`). Coordinatewise negation is a bijection of the sign cube, so summing over all inputs is unchanged by this reindexing. The squared-derivative averages, and hence the sums of coordinate influences, are equal.

**Key facts.** `FABL.sq_discreteDerivative_booleanDual`.
