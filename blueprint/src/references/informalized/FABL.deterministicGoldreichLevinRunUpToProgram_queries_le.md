<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinRunUpToProgram_queries_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership query bound for the run

**Claim.** For every $k\le n$, running the program through $k$ stages makes at most $k$ times its stage query budget in membership queries.

**Proof.** Apply the projected-cost bound through successive stages ( `FABL.deterministicGoldreichLevinRunUpToProgram_costProjection_le`) with the projection that reads the membership-query count. This projection sends zero cost to zero and preserves addition, because the query coordinate of a sum of learning costs is the sum of their query coordinates. Set the per-stage bound to the stage query budget. The controller contributes no membership queries, and the stage cost contributes exactly the restricted-weight query count, which is the stage query budget; thus every eligible stage satisfies the required per-stage bound. The projected-cost theorem then gives the stated bound for every $k\le n$.

**Key facts.** `FABL.deterministicGoldreichLevinRunUpToProgram_costProjection_le`.
