<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.exactDegreeFourierEstimatorProgram_of_decisionTree_failureProbability_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision-tree estimator guarantee

**Claim.** If a decision tree of depth at most $k$ computes the target's real-valued sign representation, then the exact-degree estimator program has failure probability at most $1/10$.

**Proof.** The Fourier degree of a function computed by the given decision tree is at most the tree's depth (FABL.fourierDegree_toReal_le_depth_of_decisionTree). Combining this with the assumed depth bound gives Fourier degree at most $k$. The estimator failure-probability theorem then applies and yields the claimed bound.

**Key facts.** `FABL.fourierDegree_toReal_le_depth_of_decisionTree`, `FABL.exactDegreeFourierEstimatorProgram_failureProbability_le_one_tenth`.

**Caveat.** The payload's informal prose describes other Fourier-learning facts; this account follows the formal decision-tree statement and its proof.
