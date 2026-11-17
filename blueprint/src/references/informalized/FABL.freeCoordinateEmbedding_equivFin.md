<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.freeCoordinateEmbedding_equivFin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate embedding evaluation

**Claim.** The embedding that enumerates the elements of a finite coordinate set sends the canonical position corresponding to an element to that element itself.

**Proof.** The embedding is formed by first applying the inverse of the canonical equivalence between the coordinate set and its finite index type, then including the resulting subtype element into the ambient coordinate type. Applying it to the index assigned to an element therefore recovers that element by the inverse-equivalence identity; the subtype inclusion then returns its underlying coordinate.
