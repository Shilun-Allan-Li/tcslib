<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinRunUpToProgram_randomExamples -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Random Examples

**Claim.** For every admissible learning input, Boolean target, and $k$ no greater than the dimension, the deterministic Goldreich–Levin program run through stage $k$ uses zero random examples.

**Proof.** Project each program cost to its random-example count. The cost-projection bound for the run through stage $k$ (`deterministicGoldreichLevinRunUpToProgram_costProjection_le`) applies because this projection is zero on the zero cost and additive under cost addition. At every stage that actually runs, the controller tick contributes no random examples, and the stage cost contributes none either: its query batch is charged only for membership queries and work. Thus every executed stage has projected cost at most zero, so the total random-example count is at most zero. Since it is a natural number, it equals zero.

**Key facts.** `FABL.deterministicGoldreichLevinRunUpToProgram_costProjection_le`.
