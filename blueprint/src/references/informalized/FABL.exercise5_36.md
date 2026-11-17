<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.exercise5_36 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Near-extremal first-level Fourier weight

**Claim.** There are Boolean functions on dimensions tending along a sequence, with positive parameters tending to zero, whose singleton coefficient at coordinate $0$ is $1-\delta_q/2$, and whose first-level Fourier weight satisfies the stated eventual lower bound for a positive constant.

**Proof.** Choose the dimensions, functions, and parameters from the established FKN optimality sequence. Its parameters are positive (`FABL.fknOptimalityDelta_pos`) and tend to zero (`FABL.tendsto_fknOptimalityDelta`); the singleton coefficient at coordinate $0$ is exactly $1-\delta_q/2$ (`FABL.fourierCoeff_fknOptimalityFunction_zero`). Take $c=1/36$, which is positive. The eventual first-level weight estimate for this sequence (`FABL.eventually_fourierWeightAtLevel_one_fknOptimalityFunction_lower`) then supplies the required inequality for all sufficiently large indices.

**Key facts.** `FABL.fknOptimalityDelta_pos`, `FABL.tendsto_fknOptimalityDelta`, `FABL.fourierCoeff_fknOptimalityFunction_zero`, `FABL.eventually_fourierWeightAtLevel_one_fknOptimalityFunction_lower`.
