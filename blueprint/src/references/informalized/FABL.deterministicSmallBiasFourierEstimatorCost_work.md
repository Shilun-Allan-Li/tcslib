<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.deterministicSmallBiasFourierEstimatorCost_work -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work of the Fourier Estimator

**Claim.** For each small-bias Fourier input and finite coordinate set $U$, the estimator's work is the sum of the deterministic small-bias construction work, the sample count, and the Fourier estimator work at that sample count and set $U$.

**Proof.** Expanding the estimator cost, the construction contributes its deterministic work, while the query-batch cost contributes $m$ units of work and the local computation contributes the Fourier estimator work at $m$ and $U$, where $m$ is the sample count. Adding these terms and reassociating the natural-number sum gives the stated identity.
