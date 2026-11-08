<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.mem_of_isRelevantJuntaRestriction_of_dependsOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relevant Coordinates of a Restriction

**Claim.** If the function depends only on coordinates in $J$, then every free coordinate whose change can alter the restricted function belongs to $J$.

**Proof.** Assume instead that the relevant free coordinate $i$ is not in $J$. Relevance provides two free assignments that agree at every coordinate other than $i$ but give different values of the restricted function. Their combined full assignments agree on every coordinate in $J$: a coordinate of $J$ that is fixed by $P$ has the same prescribed value in both, while a coordinate of $J$ outside $P$ is free and differs from $i$, so the two free assignments agree there. Since the function depends only on $J$, these full assignments must give the same value of the function. This contradicts the distinct restricted values, proving $i\in J$.
