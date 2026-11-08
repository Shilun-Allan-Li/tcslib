<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.DNFFormula.badRestrictionWeight_eq_coordSwitchingFailureProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bad Restriction Weight and Switching Probability

**Claim.** The total product weight of restrictions on which the DNF is nonconstant equals the coordinate-switching failure probability at threshold $1$ for its Boolean function.

**Proof.** Expand both quantities as finite sums over restrictions. The indicator at threshold $1$ is $1$ exactly on bad restrictions and $0$ otherwise (`FABL.coordSwitchingFailureIndicator_one_eq_badRestriction`). Thus each term in the switching-probability sum is the restriction weight on the bad restrictions and zero elsewhere. Filtering the sum to those restrictions, and identifying that filtered sum with the sum over the subtype of bad restrictions, gives precisely the bad restriction weight.

**Key facts.** `FABL.coordSwitchingFailureIndicator_one_eq_badRestriction`.
