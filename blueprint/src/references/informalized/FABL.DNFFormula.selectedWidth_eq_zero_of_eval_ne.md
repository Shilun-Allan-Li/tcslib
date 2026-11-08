<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.DNFFormula.selectedWidth_eq_zero_of_eval_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of the Unselected Term

**Claim.** If the formula does not evaluate to $-1$ at an input, then the selected term has width zero.

**Proof.** When the formula does not evaluate to $-1$, the selected-term definition takes its fallback value, the empty term. The empty term has no literals, so its width, the length of its literal list, is zero. Thus the selected width is zero.
