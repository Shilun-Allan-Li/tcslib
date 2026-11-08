<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.goldreichLevinQueryRunUpTo_work_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin work bound

**Claim.** Every supported outcome of the run through stage $k$ has local work at most $k$ times the controller work plus $2\,\mathrm{cap}(\tau)$ times the stated per-candidate work bound.

**Proof.** Apply the projected-cost theorem (`goldreichLevinQueryRunUpTo_costProjection_le`) to the projection extracting local work. It vanishes at zero cost and is additive when costs are combined. Take the per-candidate bound to be $8(m+1)(n+1)$, as supplied by the stage-estimation work theorem (`goldreichLevinStageEstimateProgram_work_le`). The projected-cost theorem then bounds each stage's contribution by the controller work plus $2\,\mathrm{cap}(\tau)$ times this candidate bound, yielding the asserted total after $k$ stages.

**Key facts.** `FABL.goldreichLevinQueryRunUpTo_costProjection_le`, `FABL.goldreichLevinStageEstimateProgram_work_le`.
