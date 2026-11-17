<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaPolynomialDegree_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Polynomial Degree

**Claim.** For every natural number $k>0$, the degree $k-\lfloor3k/4\rfloor$ is positive.

**Proof.** For positive $k$, integer division gives $3k/4<k$: indeed, $3k<4k$, so the quotient of $3k$ by $4$ is strictly less than $k$. Hence subtracting that quotient from $k$ leaves a positive natural number.
