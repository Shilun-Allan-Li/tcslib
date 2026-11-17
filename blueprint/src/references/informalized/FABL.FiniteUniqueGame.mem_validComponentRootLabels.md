<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.mem_validComponentRootLabels -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Valid Component Root Labels

**Claim.** A label belongs to the valid root label set for a component exactly when transporting it along the chosen paths satisfies every constraint whose source belongs to that component.

**Proof.** By definition, the valid root label set is the filter of all labels in `Fin q` by the predicate that the label is valid for the component. Membership in this filter is therefore equivalent to that predicate.
