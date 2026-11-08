<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaConstantTestProgram_cost_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Test Program Cost

**Claim.** Every supported outcome of the constant-testing program has cost $(m,0,2m)$, where $m$ is the specified Fourier estimator sample count.

**Proof.** The constant-testing program maps the scheduled Fourier estimator's output through the decision rule. The run law for a mapped program is the image of the original run law under that output map, with cost unchanged (`FABL.LearningProgram.runWithCost_map`). Hence any supported outcome comes from an estimator outcome with the same cost. The scheduled estimator cost formula (`FABL.scheduledFourierCoeffEstimatorProgram_cost_eq`), applied with the empty set and the specified accuracy and failure parameter, gives $(m,0,m+m(0+1))=(m,0,2m)$. Equality of these triples gives equality of costs, since the triple representation is injective (`FABL.LearningCost.toTriple_injective`).

**Key facts.** `FABL.LearningProgram.runWithCost_map`, `FABL.scheduledFourierCoeffEstimatorProgram_cost_eq`, `FABL.LearningCost.toTriple_injective`.
