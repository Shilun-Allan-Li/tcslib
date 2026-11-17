<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.DNFFormula.badRestrictionWeight_eq_zero_of_width_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Bad Weight at Width Zero

**Claim.** If a DNF has width zero, then for every real $\delta$ its total weight over nonconstant restrictions is zero.

**Proof.** Expand the bad restriction weight as a sum over restrictions that are bad. For any such restriction, badness supplies two Boolean inputs on which the restricted function differs. But width zero makes the DNF’s Boolean function constant across all sign assignments (`FABL.DNFFormula.toBooleanFunction_eq_of_width_eq_zero`); applying this to the two completions of those inputs contradicts their asserted difference. Hence there are no bad restrictions, and the sum over them is zero.

**Key facts.** `FABL.DNFFormula.toBooleanFunction_eq_of_width_eq_zero`.
