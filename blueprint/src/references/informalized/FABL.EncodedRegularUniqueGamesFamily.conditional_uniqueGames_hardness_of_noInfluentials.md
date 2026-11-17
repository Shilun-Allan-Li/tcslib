<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.EncodedRegularUniqueGamesFamily.conditional_uniqueGames_hardness_of_noInfluentials -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Unique-Games Hardness

**Claim.** The source promise problem is polynomial-time Karp reducible to the target gap promise under the stated tester, transform, and threshold hypotheses.

**Proof.** The assumed reduction from the source to the Unique Games gap promise is supplied by the gap hypothesis. The long-code reduction theorem, applied with the tester boundary obtained from the tester's predicate and arity assumptions and with the given transform, codec, and machine, reduces that Unique Games promise to the target gap promise. Composing these two promise-preserving reductions gives the claimed reduction.

**Key facts.** `FABL.IsDictatorVsNoInfluentialsTest.longCodeTestBoundary`, `FABL.EncodedRegularUniqueGamesFamily.longCodeFiniteTransform_reducesGap_of_noInfluentials`, `FABL.PromiseKarpReducible.trans`.
