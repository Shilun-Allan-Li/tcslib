<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.subset_of_card_sdiff_le_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subset from an Empty Difference

**Claim.** If the set difference $J\setminus P$ has cardinality at most zero, then $J\subseteq P$.

**Proof.** Take any $i\in J$ and suppose, for contradiction, that $i\notin P$. Then $i$ belongs to $J\setminus P$, so this difference is nonempty and has positive cardinality. That contradicts its cardinality being at most zero. Therefore every element of $J$ belongs to $P$.
