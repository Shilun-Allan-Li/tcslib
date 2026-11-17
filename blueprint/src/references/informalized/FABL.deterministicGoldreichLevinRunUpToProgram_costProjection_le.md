<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinRunUpToProgram_costProjection_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projected cost through successive stages

**Claim.** If the projection sends zero cost to zero, preserves addition, and every eligible stage contributes projected cost at most $S$, then running the program through any $k\le n$ stages has projected cost at most $kS$.

**Proof.** Proceed by induction on $k$. At $k=0$, the program returns its initial state without cost, so the projected cost is zero. For the induction step, first run the program through $k$ stages and call the resulting outcome the previous outcome. The induction hypothesis bounds the projection of its cost by $kS$. The run through $k+1$ stages is this previous run followed by the continuation selected from its output state. The cost of a bound program is the sum of the first-run and continuation costs ( `FABL.DeterministicQueryProgram.runWithCost_bind`), so addition preservation lets us bound their projections separately. Since $k+1\le n$, stage $k$ is within the dimension. If the previous state has no active set, or its active set exceeds the cap, the continuation is pure and costs zero. Otherwise it executes the stage-step program; its cost is the controller cost plus the stage cost ( `FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageStepProgram`), so the assumed stage bound applies. In every case the continuation's projected cost is at most $S$. Adding this to the induction bound gives $kS+S=(k+1)S$, completing the induction.

**Key facts.** `FABL.DeterministicQueryProgram.runWithCost_bind`, `FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageStepProgram`.
