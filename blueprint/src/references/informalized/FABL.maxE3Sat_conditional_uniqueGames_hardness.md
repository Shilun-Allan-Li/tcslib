<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.maxE3Sat_conditional_uniqueGames_hardness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Max-E3-SAT hardness

**Claim.** Under the stated Unique Games reduction, test, finite transformation, and codec hypotheses, the source promise problem reduces to the promise problem of distinguishing target optimum at least $1-\delta$ from optimum at most $7/8+\delta$.

**Proof.** Apply the conditional Unique Games hardness theorem (`conditional_uniqueGames_hardness`) to Håstad’s Max-E3-SAT dictator-vs.-no-notables test at parameter $\delta/2$ (`hastadThreeSat_dictatorVsNoNotables`). This test has completeness $1$ and soundness $7/8+\delta/2$, with the replacement error specified in the hypotheses. Its predicate family and tester give the required test boundary (`longCodeTestBoundary`). The assumed finite transformation, codec, and machine produce the reduction to the target optimization problem. The hypotheses on Unique Games completeness and soundness, together with the assumed completeness and soundness estimates, meet the corresponding conditions of the conditional theorem. The target thresholds are $7/8+\delta$ and $1-\delta$, whose strict separation is assumed. The theorem therefore gives the stated promise reduction.

**Key facts.** `FABL.hastadThreeSat_dictatorVsNoNotables`, `FABL.IsDictatorVsNoNotablesTest.longCodeTestBoundary`, `FABL.EncodedRegularUniqueGamesFamily.conditional_uniqueGames_hardness`.
