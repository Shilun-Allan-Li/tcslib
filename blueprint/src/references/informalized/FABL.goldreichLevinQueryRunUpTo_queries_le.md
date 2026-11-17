<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.goldreichLevinQueryRunUpTo_queries_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin query complexity

**Claim.** Every supported outcome of the run through stage $k$ uses at most $k\cdot 2\,\mathrm{cap}(\tau)\cdot 2m$ membership queries, where $m$ is the stated estimator sample count.

**Proof.** Apply the projected-cost theorem (`goldreichLevinQueryRunUpTo_costProjection_le`) to the projection that extracts the number of membership queries. This projection is zero at zero cost and additive under the program's cost composition. Use the stage query bound (`goldreichLevinStageEstimateProgram_queries_le`) with candidate bound $2m$. The general projected-cost conclusion then gives a per-stage allowance of one controller projection plus $2\,\mathrm{cap}(\tau)\cdot 2m$. The controller contributes no membership queries, so this is precisely the claimed bound after $k$ stages.

**Key facts.** `FABL.goldreichLevinQueryRunUpTo_costProjection_le`, `FABL.goldreichLevinStageEstimateProgram_queries_le`.
