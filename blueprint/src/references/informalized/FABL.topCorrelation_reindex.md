<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.topCorrelation_reindex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reindexing Top Correlation

**Claim.** Reindexing sign assignments along a bijection of finite coordinate sets leaves the top correlation unchanged.

**Proof.** Expand the top correlations as averages. Reindex the average over assignments on $I$ along the bijection induced by $e$; the expectation over the reindexed assignments is the same as the original expectation because this map is an equivalence. For each assignment, the product of all coordinate signs is also unchanged: reindexing the finite product along the bijection $e$ gives the product over the target coordinates. Thus the two averages agree.
