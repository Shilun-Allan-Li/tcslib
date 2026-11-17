<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.three_mul_lowDegreeJuntaPolynomialDegree_le_cutoff_add_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Junta Polynomial Degree Bound

**Claim.** For every natural number $k$, three times the low-degree junta polynomial degree at cutoff parameter $k$ is at most the low-degree junta cutoff at $k$ plus three.

**Proof.** Substitute the definitions: the claim becomes $3(k-\lfloor 3k/4\rfloor)\le \lfloor 3k/4\rfloor+3$, where the floor notation expresses natural-number division by $4$. Write $k=4q+r$ with $0\le r<4$. Then $\lfloor3k/4\rfloor=3q+\lfloor3r/4\rfloor$, and the desired inequality reduces to $3r-3\lfloor3r/4\rfloor\le\lfloor3r/4\rfloor+3$. Checking $r=0,1,2,3$ verifies it in each case.
