<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.freeCoordinates_coordRestrictionOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free coordinates of a restriction

**Claim.** The free coordinates of the coordinate restriction formed from $J$ and fixed signs outside $J$ are exactly $J$.

**Proof.** Check membership coordinate by coordinate. If $i\in J$, the restriction assigns the free status at $i$, so $i$ belongs to the set of free coordinates. If $i\notin J$, the restriction value is the fixed status determined by the assigned sign (`coordRestrictionOf_apply_of_not_mem`); either possible fixed status differs from free. Thus no coordinate outside $J$ is free, proving equality of the two finite sets.

**Key facts.** `FABL.coordRestrictionOf_apply_of_not_mem`.
