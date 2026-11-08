<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.exactlyThreePaddingLiteral_index_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct padding coordinates

**Claim.** Distinct coordinates among the three additional variables yield padding literals with distinct variable indices, whatever their required signs.

**Proof.** The padding literal indexed by a coordinate $i$ has variable index given by the natural-add embedding of $i$ after the original $n$ coordinates. If two such variable indices were equal, injectivity of that embedding (`Fin.natAdd_injective`) would imply that the two coordinates were equal, contradicting their assumed distinctness. The required signs do not affect the indices.
