<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.card_addressingRelevantCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Relevant Coordinates

**Claim.** For any sign assignment on $m+2^m$ coordinates, the set of its $m$ address coordinates together with the data coordinate selected by its address has cardinality at most $m+1$.

**Proof.** The set of relevant coordinates is obtained by adjoining the single selected data coordinate to the image of the $m$ address coordinates. Adjoining one element increases cardinality by at most one. The address-coordinate map is injective: equality of two image coordinates, after applying the inverse of the sum-fin equivalence, gives equality of the corresponding left-summand indices. Therefore its image has exactly $m$ elements, and the relevant set has cardinality at most $m+1$.
