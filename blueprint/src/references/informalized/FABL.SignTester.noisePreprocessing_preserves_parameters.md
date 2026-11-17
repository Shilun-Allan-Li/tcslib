<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.SignTester.noisePreprocessing_preserves_parameters -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Preprocessing Preserves Parameters

**Claim.** Under the stated completeness and soundness hypotheses, preprocessing gives the dictator lower bound $\beta-r\delta/2$ and preserves the soundness upper bound $\alpha+\mathrm{error}$ for functions with small stable influences.

**Proof.** For completeness, fix a coordinate dictator. The tester's dictator noise bound, using the common arity $r$, says its preprocessed acceptance probability is at least its original acceptance probability minus $r\delta/2$. The original probability is at least $\beta$ by hypothesis, so the preprocessed probability is at least $\beta-r\delta/2$. For soundness, take any admissible function with small stable influences. The noise-preprocessing identity rewrites its preprocessed acceptance probability as the original tester's acceptance probability on the function after applying the noise operator with correlation $1-\delta$. The assumed soundness bound applies to that function and gives the upper bound $\alpha+\mathrm{error}$. These are the two required conclusions.

**Key facts.** `FABL.SignTester.noisePreprocessedAcceptanceProbability_dictator_ge`, `FABL.SignTester.noisePreprocessedAcceptanceProbability_eq_noiseOperator`.
