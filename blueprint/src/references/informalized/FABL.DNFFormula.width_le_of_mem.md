<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFFormula.width_le_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Term Width Bounded by Formula Width

**Claim.** Every term appearing in a DNF formula has width at most the formula’s width.

**Proof.** The formula width is the fold of the term widths using maximum, initialized at zero. For any term in the list, its width is at most the value of this fold (`FABL.DNFFormula.le_foldl_max`): at the step where that term occurs, the running maximum is at least its width, and subsequent maxima cannot decrease it. Applying this to the given term proves the bound.

**Key facts.** `FABL.DNFFormula.le_foldl_max`.
