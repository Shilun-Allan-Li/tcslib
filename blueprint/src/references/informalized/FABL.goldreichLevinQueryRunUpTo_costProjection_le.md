<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.goldreichLevinQueryRunUpTo_costProjection_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projected cost through partial runs

**Claim.** Under the stated additivity and stage-cost hypotheses, every supported outcome of the run through $k$ stages has projected cost at most $k$ times the controller cost plus $2$ times the active cap times the candidate bound.

**Proof.** Proceed by induction on $k$. At $k=0$, the run returns the initial state at zero cost, so the result follows from the assumption that the projection vanishes at zero. For the step from $k$ to $k+1$, express a supported outcome as a supported outcome of the first $k$ stages followed by a supported continuation; this decomposition follows from the support law for running a bound program (`runWithCost_bind`). The induction hypothesis bounds the previous cost by $k$ stage allowances. For the continuation, if the previous state has no active family, or if its family exceeds the cap, the algorithm returns immediately at zero additional cost. Otherwise it runs one stage. The stage-step law (`runWithCost_goldreichLevinStageStepProgram`) separates the controller charge from the stage-estimation cost. By the stage hypothesis, the latter is at most the number of candidates times the candidate bound. Each active set contributes at most two children, so the candidate count is at most twice the active-set size (`card_goldreichLevinCandidates_le_two_mul`), and the size is at most the cap in this branch. Additivity of the projection therefore bounds the continuation by one controller charge plus $2$ times the cap times the candidate bound. Combining this with the induction bound gives the claimed $(k+1)$-stage estimate.

**Key facts.** `FABL.LearningProgram.runWithCost_bind`, `FABL.runWithCost_goldreichLevinStageStepProgram`, `FABL.card_goldreichLevinCandidates_le_two_mul`.
