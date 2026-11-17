<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.deterministicSmallBiasFourierEstimatorCost_randomExamples -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Random-Example Cost

**Claim.** For every small-bias Fourier input and every finite coordinate set $U$ in its dimension, the estimator uses zero random examples.

**Proof.** By definition, the estimator cost is the sum of a construction cost whose random-example component is $0$ and a Fourier-estimation cost. The latter is a query-batch cost plus a local-work cost, both with random-example component $0$. Addition of costs adds these components, so the resulting random-example cost is $0$.
