<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaMatchingIndexEmbedding_matches -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected Samples Match the Assignment

**Claim.** If $M$ is at most the number of samples whose coordinates on $P$ agree with $z$, then each sample selected by the canonical order-preserving injection from the first $M$ indices into those matching indices agrees with $z$ on $P$.

**Proof.** The selected index belongs to the filtered set of matching indices: the canonical order embedding into that set sends every selected index to one of its members. Membership in the filtered set means that the selected sample's fixed part equals $z$. Evaluating this equality at any coordinate in $P$ gives the required agreement.
