<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.sum_influence_relevantCoordinates_eq_totalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence on Relevant Coordinates

**Claim.** For every real-valued function on the sign cube, the sum of its influences over coordinates with strictly positive influence equals its total influence.

**Proof.** The total influence sums over every coordinate, while the left side retains only those with positive influence. By nonnegativity of influence (`FABL.influence_nonneg`), a coordinate that is not relevant has influence at most zero and at least zero, hence exactly zero. Removing all such zero terms leaves the total sum unchanged.

**Key facts.** `FABL.influence_nonneg`.
