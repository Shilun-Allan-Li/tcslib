<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.functionAlgebraicDegree_reindexedJuntaRestriction_le_of_no_detection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound when no frequency is detected

**Claim.** Under the stated junta, accuracy, and no-detection hypotheses, the algebraic degree of the binary encoding of the reindexed restriction is at most the specified polynomial degree.

**Proof.** The reindexed restriction is a $k$-junta (`reindexedJuntaRestriction_isKJunta`), since the target depends only on the set $J$ of at most $k$ coordinates. The accurate Fourier estimates together with the absence of a detected low-degree frequency imply that this restriction is correlation immune through order $\operatorname{lowDegreeJuntaCutoff}(k)$ (`isCorrelationImmune_of_no_lowDegreeJuntaDetection`). The degree bound for a $k$-junta that is correlation immune through order $d$ (`functionAlgebraicDegree_encoding_le_sub_of_isKJunta_of_isCorrelationImmune`) now bounds the encoded algebraic degree by $k-d$. With $d=\operatorname{lowDegreeJuntaCutoff}(k)$, this is exactly the specified polynomial degree.

**Key facts.** `FABL.reindexedJuntaRestriction_isKJunta`, `FABL.isCorrelationImmune_of_no_lowDegreeJuntaDetection`, `FABL.functionAlgebraicDegree_encoding_le_sub_of_isKJunta_of_isCorrelationImmune`.
