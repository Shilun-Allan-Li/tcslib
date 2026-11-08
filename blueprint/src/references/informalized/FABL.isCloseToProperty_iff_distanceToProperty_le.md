<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BLR.lean :: FABL.isCloseToProperty_iff_distanceToProperty_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closeness to a Property

**Claim.** A function is within distance $\epsilon$ of a nonempty property exactly when its distance to that property is at most $\epsilon$.

**Proof.** If some member $g$ of the property is within distance $\epsilon$, the distance to the property is no greater than the distance to $g$ ( `distanceToProperty_le`), hence is at most $\epsilon$. Conversely, the closest member belongs to the property ( `closestInProperty_mem`). If the distance to the property is at most $\epsilon$, this member witnesses closeness to the property by the definition of distance to the property.

**Key facts.** `FABL.distanceToProperty_le`, `FABL.closestInProperty_mem`.
