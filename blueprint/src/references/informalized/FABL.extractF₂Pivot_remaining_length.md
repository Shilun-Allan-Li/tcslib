<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.extractF₂Pivot_remaining_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length After Pivot Extraction

**Claim.** If extraction returns a pivot and a remaining list, then the remaining list has length one less than the original list.

**Proof.** Induct on the original list. Extraction cannot succeed on the empty list. For a nonempty list, if the head is the pivot, the remainder is exactly the tail, whose length is one less than the original list's length. Otherwise extraction must succeed recursively on the tail. By the induction hypothesis, the recursive remainder has length one less than the tail. The original extraction adds the skipped head to that remainder, increasing its length by one; hence the resulting remainder has length one less than the original list.
