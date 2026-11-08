<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.card_influentialCoordinates_learningConsequencesThreshold_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influential-coordinate cap

**Claim.** If the target’s total influence is at most $t$, then the number of coordinates whose Boolean influence is at least the learning-consequences threshold is at most the learning-consequences coordinate cap.

**Proof.** The threshold is positive, by positivity of the learning-consequences threshold (\(\texttt{learningConsequencesThreshold\_pos}\)). The influential-coordinate counting bound (\(\texttt{card\_influentialCoordinates\_le\_div}\)) therefore gives that their number is at most the total influence divided by the threshold. Using the assumed total-influence bound and positivity of the threshold, this quotient is at most \(t\) divided by the threshold, hence at most \(2t\) divided by the threshold since \(t>0\). Finally, the ceiling defining the coordinate cap is at least this last quantity; translating the real-valued inequalities back to natural-number cardinalities gives the claimed bound.

**Key facts.** `FABL.learningConsequencesThreshold_pos`, `FABL.card_influentialCoordinates_le_div`.
