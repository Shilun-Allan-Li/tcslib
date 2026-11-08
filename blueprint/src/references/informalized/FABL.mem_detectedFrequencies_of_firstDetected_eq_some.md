<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.mem_detectedFrequencies_of_firstDetected_eq_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First detected frequency membership

**Claim.** If the first-detection rule returns $S$, then the underlying frequency $S.1$ belongs to the detected-frequency set.

**Proof.** The detected-frequency set must be nonempty: if it were empty, the rule would return `none`, contradicting the hypothesis that it returns `some S`. Let $T$ be the element selected by the rule, namely the element corresponding to index zero under the finite-set equivalence with an initial segment. By construction, $T$ belongs to the detected-frequency set. Applying the underlying-set map to the equality asserting that the rule returns `some S` shows that $T.1=S.1$. Hence $S.1$ also belongs to the detected-frequency set.
