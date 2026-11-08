<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.SignTester.noisePreprocessedAcceptanceProbability_eq_noiseOperator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Preprocessing Identity

**Claim.** A tester's acceptance probability after independently noise-preprocessing each check's queries equals its acceptance probability on the function obtained by applying the noise operator with correlation $1-\delta$.

**Proof.** Both probabilities average over the same seed law. Fix a seed: the selected check's preprocessed value equals its randomized value on the function after applying the noise operator (`SignQueryCheck.noisePreprocessedValue_eq_noiseOperator`). Thus the two functions of the seed being averaged agree at every seed, and their expectations are equal.

**Key facts.** `FABL.SignQueryCheck.noisePreprocessedValue_eq_noiseOperator`.
