<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.card_tribesRestCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality After Removing a Coordinate

**Claim.** Removing a coordinate from its block leaves a set of cardinality $w-1$.

**Proof.** The chosen coordinate belongs to the block containing it (`mem_tribesBlockCoordinates_self`). That block has cardinality $w$ (`card_tribesBlockCoordinates`). Removing one member of a finite set decreases its cardinality by one, so the remaining set has cardinality $w-1$.

**Key facts.** `FABL.mem_tribesBlockCoordinates_self`, `FABL.card_tribesBlockCoordinates`.
