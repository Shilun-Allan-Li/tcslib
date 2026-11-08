<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.recursiveJuntaLearnerAux_work_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Work Bound

**Claim.** For every fuel $r$, fixed-coordinate set, assignment, and supported outcome of the recursive learner, the charged local work is at most $T(r)W(\varepsilon)$, where $T(0)=1$ and $T(r+1)=1+2T(r)$.

**Proof.** Apply the recursive cost-projection bound to the projection that reads the local-work component. This projection is zero on zero cost and additive under cost addition. For every supported node-finder outcome, its pathwise cost guarantee bounds local work by the finder’s declared work bound $W(\varepsilon)$. The recursive projection bound therefore yields a total work of at most the number of recursive calls, $T(r)$, multiplied by $W(\varepsilon)$.

**Key facts.** `FABL.recursiveJuntaLearnerAux_costProjection_le`.
