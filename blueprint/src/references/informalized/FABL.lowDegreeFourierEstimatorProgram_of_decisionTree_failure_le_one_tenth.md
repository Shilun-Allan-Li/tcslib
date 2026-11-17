<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.lowDegreeFourierEstimatorProgram_of_decisionTree_failure_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Learning from a decision tree

**Claim.** If the target is computed by a decision tree, then running the low-degree estimator at the decision-tree learning degree gives failure probability at most $1/10$.

**Proof.** First, the positive learning parameter satisfies $0<\varepsilon\le1/2$, so $\varepsilon/2$ lies in $(0,1]$. The target, transported to the binary cube, is sign-valued. The decision-tree concentration theorem therefore gives Fourier concentration up to the truncation degree at parameter $\varepsilon/2$. The proof identifies the transported target with the target’s real-valued version on the sign cube, and the definition of the decision-tree learning degree identifies the truncation degree with the estimator’s degree parameter. The low-degree estimator’s failure guarantee under this concentration hypothesis now yields the bound $1/10$.

**Key facts.** `FABL.F₂DecisionTree.isFourierSpectrumConcentratedUpTo_of_decisionTree`, `FABL.lowDegreeFourierEstimatorProgram_failureProbability_le_one_tenth`, `FABL.positiveLearningParameter_toReal_mem_Ioc`, `FABL.signValue_eq_neg_one_or_one`.
