<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oddBLRQueryNoise_parameter_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness and Soundness of the Noisy Test

**Claim.** Under the stated parameter hypotheses, every dictator is accepted by the Håstad test with probability at least $1-\delta$, and every bounded function whose stable influences are at most $\varepsilon$ has acceptance probability at most $1/2+\sqrt{\varepsilon}/2$.

**Proof.** Put $\eta=2\delta/3$ and $\rho=1-\eta$. The noise-rate bound (`oddBLRQueryNoiseRate_mem_Icc`) ensures $\eta\in[0,1]$ and hence $\rho\in[0,1]$. The cutoff hypothesis becomes $\varepsilon\le 1-\rho^2$. Apply the parameter-preservation theorem for noise preprocessing (`SignTester.noisePreprocessing_preserves_parameters`) to the base odd BLR tester, with arity three. Its completeness input holds because a dictator has acceptance probability $1$ in the base test, as given by the dictator acceptance formula (`hastadAcceptanceProbability_dictator`). Its soundness input is the bound for the noisy odd BLR test under the cutoff and stable-influence hypotheses (`oddBLRAcceptanceProbability_noise_le`). Parameter preservation therefore gives the two desired bounds for the preprocessed tester. Finally, the preprocessed tester’s acceptance probability agrees with the noise-preprocessed probability (`SignTester.noisePreprocessed_acceptanceProbability`). In the completeness bound, the preserved loss is $3\eta/2=\delta$, by the definition of $\eta$; the soundness bound is unchanged.

**Key facts.** `FABL.oddBLRQueryNoiseRate_mem_Icc`, `FABL.SignTester.noisePreprocessing_preserves_parameters`, `FABL.hastadAcceptanceProbability_dictator`, `FABL.oddBLRAcceptanceProbability_noise_le`, `FABL.SignTester.noisePreprocessed_acceptanceProbability`.
