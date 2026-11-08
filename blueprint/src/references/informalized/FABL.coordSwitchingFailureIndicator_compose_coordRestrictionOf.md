<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordSwitchingFailureIndicator_compose_coordRestrictionOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching Failure under Composed Restrictions

**Claim.** The switching failure indicator under the composed assignment equals the indicator for the function on the free coordinates, reindexed by their increasing enumeration, with the corresponding restrictions.

**Proof.** By definition, each switching failure indicator is determined by whether the decision-tree depth of the associated restricted function is at least $k$. The depth of the restriction under the composed assignment equals the depth of the reindexed function under the restrictions on the free coordinates (\texttt{FABL.decisionTreeDepth_restrict_compose_coordRestrictionOf}). Thus the two threshold comparisons agree, and so do the indicators.

**Key facts.** `FABL.decisionTreeDepth_restrict_compose_coordRestrictionOf`.
