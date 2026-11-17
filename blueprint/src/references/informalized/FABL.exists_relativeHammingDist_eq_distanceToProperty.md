<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BLR.lean :: FABL.exists_relativeHammingDist_eq_distanceToProperty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainment of distance to a property

**Claim.** For a function on a finite nonempty domain and a nonempty property of functions, some member of the property has relative Hamming distance from the given function equal to the distance to that property.

**Proof.** Take the chosen closest member of the property. The closest-member existence result ensures that this function belongs to the property (`FABL.closestInProperty_mem`). By definition, the distance to the property is the relative Hamming distance to that same chosen function. Thus it is the required member, and the equality holds by the definition of the distance.

**Key facts.** `FABL.closestInProperty_mem`.
