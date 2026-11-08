<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RawCSPInstance.value_restrictAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value Is Preserved by Restriction

**Claim.** For every assignment to all variables, its restriction to participating variables has the same value in the instance with isolated variables removed as it has in the original raw instance.

**Proof.** Expand the two value definitions. Each constraint occurrence in the reduced instance is an attached occurrence of an original constraint, with its scope lifted to participating variables. By satisfaction-indicator preservation (`participatingConstraint_satisfiedIndicator`), each such occurrence contributes the same indicator as its original constraint. The sum over attached occurrences is the sum over the original multiset, since attaching and then mapping the original value recovers that multiset sum. The constraint counts also agree: attaching preserves cardinality, and mapping the attached constraints preserves it because each occurrence contributes once. Thus the numerators and denominators agree, so the values are equal.

**Key facts.** `FABL.RawCSPInstance.participatingConstraint_satisfiedIndicator`.
