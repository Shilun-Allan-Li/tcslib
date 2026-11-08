<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicQuery.lean :: FABL.DeterministicQueryProgram.runWithCost_toLearningProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic programs as learning programs

**Claim.** Interpreting a deterministic query program as a learning program that makes membership queries gives a point-mass law concentrated on the deterministic run's output and cost.

**Proof.** Proceed by induction on the deterministic program. A pure output translates to a pure learning program, so both executions return that output at zero cost, giving the claimed point mass. For a batch of queries, the translated program first uses the query-input batch program. That batch returns, deterministically, the inputs paired with their target values and charges $m$ queries and $m$ units of work (`runWithCost_queryInputBatchProgram`). The bind execution rule decomposes the translated run into this batch and the continuation (`LearningProgram.runWithCost_bind`). Apply the induction hypothesis to the continuation, with the target answers to the batch as its oracle responses. Combining the batch cost with the continuation cost gives exactly the deterministic batch run, so the resulting law is concentrated at that outcome. Finally, for a tick, the induction hypothesis gives a point mass for the continuation; adding the same tick charge on both sides preserves that point mass and matches the deterministic run.

**Key facts.** `FABL.LearningProgram.runWithCost_bind`, `FABL.runWithCost_queryInputBatchProgram`.
