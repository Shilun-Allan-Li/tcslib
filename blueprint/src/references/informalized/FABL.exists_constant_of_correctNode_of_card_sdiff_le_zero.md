<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.exists_constant_of_correctNode_of_card_sdiff_le_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Correct Decision with No Free Relevant Coordinates Is Constant

**Claim.** If a function depends only on coordinates in $J$, and $|J\setminus P|\le0$, then any correct decision for its restriction after fixing the coordinates in $P$ must be constant.

**Proof.** If the decision is already constant, its returned sign is the required value. Otherwise it is a relevant-coordinate decision, at some free coordinate $i\notin P$. Correctness says that this coordinate is relevant to the restricted function. Since the target depends only on $J$, any coordinate relevant to this restriction must belong to $J$ (`FABL.mem_of_isRelevantJuntaRestriction_of_dependsOn`). Thus $i\in J\setminus P$. But a finite set of cardinality at most zero is empty, so the assumed bound implies $J\subseteq P` (`FABL.subset_of_card_sdiff_le_zero`). This contradicts $i\notin P$. The relevant case is therefore impossible, leaving only a constant decision.

**Key facts.** `FABL.mem_of_isRelevantJuntaRestriction_of_dependsOn`, `FABL.subset_of_card_sdiff_le_zero`.
