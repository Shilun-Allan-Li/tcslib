<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.optimalComponentLabels_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of the Selected Component Label

**Claim.** If a component has at least one valid root label, then its selected component label is valid.

**Proof.** The assumed valid root label belongs to the finite set of valid component root labels, by the characterization of membership in that set (`mem_validComponentRootLabels`). Thus this set is nonempty. By the definition of the selected component label, it is chosen from this nonempty set; the chosen element belongs to the set by the defining property of choice. Applying the same membership characterization shows that the selected label is valid.

**Key facts.** `FABL.FiniteUniqueGame.mem_validComponentRootLabels`.
