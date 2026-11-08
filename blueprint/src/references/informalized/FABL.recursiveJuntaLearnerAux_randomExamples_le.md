<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.recursiveJuntaLearnerAux_randomExamples_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random Example Cost Bound

**Claim.** For every fuel $r$ and every supported outcome of the recursive learner, the number of random examples charged is at most $T(r)$ times the node finder’s random-example bound, where $T(r)$ is the recursive call count.

**Proof.** Use the recursive cost-projection bound with the projection that reads the random-example component. It sends zero cost to zero and preserves addition, so the bound applies across the recursive calls. For each supported node-finder outcome, the finder’s pathwise cost guarantee bounds its random-example component by its declared random-example bound. Feeding this node bound into the recursive projection result gives the stated total bound, namely the call count times the node bound.

**Key facts.** `FABL.recursiveJuntaLearnerAux_costProjection_le`.
