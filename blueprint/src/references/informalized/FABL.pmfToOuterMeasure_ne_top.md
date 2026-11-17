<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.pmfToOuterMeasure_ne_top -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite PMF Outer Measure

**Claim.** For any type $\alpha$, probability mass function $p$ on $\alpha$, and set $E\subseteq\alpha$, the outer measure assigned to $E$ by $p$ is not infinite.

**Proof.** By monotonicity of the outer measure, the measure of $E$ is at most that of the whole space, since $E\subseteq\alpha$. The total outer measure of a probability mass function is $1$, as follows from its total mass being one. Hence the measure of $E$ is at most $1$, which is finite and in particular is not $\infty$.
