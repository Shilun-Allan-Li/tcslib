<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialCoordinate_eq_of_same_zVariable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Special Coordinate Is Statistic-Determined

**Claim.** If two hard-sample statistics under the same protocol both equal $z$, then the samples have the same special coordinate.

**Proof.** The special-coordinate determination lemma says that whenever a sample yields $z$, its special coordinate equals the special-coordinate component of $z$ (`specialCoordinate_eq_of_zVariable_eq`). Apply it to each sample. Both special coordinates therefore equal the same component of $z$, and hence equal one another.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialCoordinate_eq_of_zVariable_eq`.
