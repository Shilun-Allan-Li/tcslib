<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.paddedCloneTupleEquiv_fst_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction of a padded tuple

**Claim.** The first component of the tuple obtained by splitting a function on the first $a$ coordinates and the remaining coordinates, evaluated at $i$, is its value at the image of $i$ in $\mathrm{Fin}(r)$.

**Proof.** By definition, the equivalence first splits a function according to whether an index lies in the initial segment, then reindexes that segment using the inverse of the initial-segment equivalence. Evaluating the first component at $i$ therefore evaluates the original function at the image of $i$, namely its cast into $\mathrm{Fin}(r)$.
