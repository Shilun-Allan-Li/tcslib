<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.DNFTerm.restrictedWidthOf_le_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted width is bounded by term width

**Claim.** For any coordinate restriction, the restricted width of a DNF term is at most its width, the number of literals in the term.

**Proof.** If some literal is falsified, the restricted width is zero and hence is at most the term width. Otherwise the restricted width counts the literals whose coordinates are free. A filtered list cannot be longer than the original list, so this count is at most the number of literals.
