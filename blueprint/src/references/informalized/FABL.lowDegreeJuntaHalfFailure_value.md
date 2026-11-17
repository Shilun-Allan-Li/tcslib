<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaHalfFailure_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halved Failure Parameter Value

**Claim.** For every rational failure parameter $\delta$ with $0<\delta\le1/2$, the value of its halved failure parameter is $\delta/2$.

**Proof.** The halved parameter is defined by the subtype constructor whose first component is the original parameter divided by $2$. Projecting to that first component gives the stated value directly from the definition.
