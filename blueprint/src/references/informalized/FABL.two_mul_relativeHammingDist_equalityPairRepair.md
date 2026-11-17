<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingExercises.lean :: FABL.two_mul_relativeHammingDist_equalityPairRepair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repairing equality pairs

**Claim.** For a Boolean string on \(2n\) coordinates, twice its relative Hamming distance from the string repaired by copying each pair's first entry equals the fraction of pairs whose entries differ.

**Proof.** First express relative Hamming distance as the uniform probability of a coordinate mismatch, using the equality between disagreement probability and relative Hamming distance (\(\texttt{FABL.uniformProbability_ne_eq_relativeHammingDist}\)). Reindex the coordinates by pairs \((i,\text{side})\), so the uniform average is an average first over pairs and then over the two sides. The repair copies the first entry to both sides (\(\texttt{FABL.equalityPairRepair_pair}\)). Consequently, the first side never mismatches; the second side mismatches exactly when the original pair's entries differ. Averaging over the two sides gives half the indicator that the pair differs. Multiplying by two and averaging over pairs yields precisely the fraction of unequal pairs.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.equalityPairRepair_pair`.
