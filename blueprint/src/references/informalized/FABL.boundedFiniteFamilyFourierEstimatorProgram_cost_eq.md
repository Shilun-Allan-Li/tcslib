<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.boundedFiniteFamilyFourierEstimatorProgram_cost_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator Cost

**Claim.** Every outcome in the support of the bounded-family Fourier estimator has cost $(|\mathcal F|m,0,|\mathcal F|m+|\mathcal F|m(n+1))$, where $m$ is its bounded-family sample count.

**Proof.** The program is the finite-family estimator run with $m$ samples per family member. Its run-with-cost law is the image of the sample-input law under the map that constructs the estimator output and assigns the cost $(|\mathcal F|m,0,|\mathcal F|m+W)$, with local work $W=|\mathcal F|m(n+1)$. Any point in the support of an image law is the image of some input in the support of the original law. Hence every supported outcome has exactly that assigned cost, which simplifies to the claimed triple.
