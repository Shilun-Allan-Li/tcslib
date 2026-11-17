<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.boolTruthTableLiftTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability of the Lifted Tester

**Claim.** The lifted tester on the concatenated input $(w,p)$ has the same acceptance probability as $T$ on the sign-valued function encoded by $p$.

**Proof.** Unfold both acceptance probabilities as expectations over the same seed distribution. Their integrands agree seed by seed: for any fixed seed, the lifted tester’s transcript, after converting Boolean answers to signs, is exactly the transcript of $T$ on the function encoded by the proof table. The lifted tester applies its acceptance predicate to precisely this converted transcript, so the two indicators of acceptance coincide for every seed. Their expectations are therefore equal.

**Key facts.** `FABL.boolTruthTableLiftTester_visibleTranscript`.
