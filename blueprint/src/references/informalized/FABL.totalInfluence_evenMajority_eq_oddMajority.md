<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EvenMajority.lean :: FABL.totalInfluence_evenMajority_eq_oddMajority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Majority Influence Equality

**Claim.** If $f$ is a majority function on the $(2m+2)$-dimensional cube, then its total influence equals that of majority on the $(2m+1)$-dimensional cube.

**Proof.** First, the total influence of any majority function on the $(2m+2)$-dimensional cube equals that of the canonical majority function in that dimension (`FABL.totalInfluence_eq_majority_of_isMajorityFunction`). Apply the same fact to the lifted odd-dimensional majority, which is itself a majority function (`FABL.liftedOddMajority_isMajorityFunction`); this identifies the canonical even-dimensional majority's total influence with that of the lift. Finally, the lifted odd-dimensional majority has the same total influence as majority on the $(2m+1)$-dimensional cube (`FABL.totalInfluence_liftedOddMajority`). Chaining these equalities proves the result.

**Key facts.** `FABL.totalInfluence_eq_majority_of_isMajorityFunction`, `FABL.liftedOddMajority_isMajorityFunction`, `FABL.totalInfluence_liftedOddMajority`.
