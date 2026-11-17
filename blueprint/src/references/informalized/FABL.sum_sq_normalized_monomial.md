<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.sum_sq_normalized_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Monomial Sum

**Claim.** For a coordinate subset $S$, summing the squared monomial divided by the square of the cube's cardinality over the sign cube gives the reciprocal of the cube's cardinality.

**Proof.** Every monomial on the sign cube has square $1$ (`monomial_sq`). Thus each summand reduces to the reciprocal of the cube's cardinality squared. There is one summand for each point of the cube, so summing gives the reciprocal of its cardinality. The cardinality is positive, allowing the stated divisions.

**Key facts.** `FABL.monomial_sq`.
