<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.maxE3Lin_conditional_uniqueGames_hardness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Max-E3-Lin hardness

**Claim.** Under the stated Unique Games reduction, test, finite transformation, and codec hypotheses, the source promise problem reduces to the promise problem of distinguishing target optimum at least $1-\delta$ from optimum at most $1/2+\delta$.

**Proof.** Apply the conditional Unique Games hardness theorem (`conditional_uniqueGames_hardness`) to the dictator-vs.-no-notables test supplied by Håstad’s Max-E3-Lin construction (`hastad_dictatorVsNoNotables`). The test has soundness threshold $1/2$, completeness threshold $1-\delta/2$, and error function given by the stated Håstad soundness error. Its predicate family and tester provide the required test boundary (`longCodeTestBoundary`). The assumed transformation, output codec, and machine then give the reduction to the target optimization problem. The hypotheses on the Unique Games completeness and soundness, and the assumed completeness estimate, discharge the corresponding conditions of the conditional theorem. For soundness, its required error term is twice the test’s error at $\delta/2$; by definition this is the error at $\delta$, since $2(\delta/2)=\delta$. The assumed soundness inequality therefore supplies the remaining condition, yielding the claimed reduction.

**Key facts.** `FABL.hastad_dictatorVsNoNotables`, `FABL.IsDictatorVsNoNotablesTest.longCodeTestBoundary`, `FABL.EncodedRegularUniqueGamesFamily.conditional_uniqueGames_hardness`.
