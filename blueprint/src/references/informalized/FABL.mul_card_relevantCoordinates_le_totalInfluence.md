<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.mul_card_relevantCoordinates_le_totalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relevant Coordinates and Total Influence

**Claim.** If every relevant coordinate has influence at least $a$, then $a$ times the number of relevant coordinates is at most the total influence.

**Proof.** The total influence is the sum of the influences over the relevant coordinates (`sum_influence_relevantCoordinates_eq_totalInfluence`). The sum of the constant value $a$ over this finite set equals $a$ times its cardinality. For each coordinate in the set, relevance holds by the membership characterization (`mem_relevantCoordinates`), so its influence is at least $a$ by hypothesis. Summing these termwise inequalities gives the desired bound.

**Key facts.** `FABL.sum_influence_relevantCoordinates_eq_totalInfluence`, `FABL.mem_relevantCoordinates`.
