<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordRestrictionWeightAt_negateState -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance under state negation

**Claim.** Negating the fixed state of a coordinate restriction leaves its coordinate weight unchanged.

**Proof.** Check the three restriction states. Negation leaves a free state free, and swaps `fixOne` with `fixNegOne`. The free state has weight $\delta$, while both fixed states have weight $(1-\delta)/2$. Hence the weight is unchanged in each case.
