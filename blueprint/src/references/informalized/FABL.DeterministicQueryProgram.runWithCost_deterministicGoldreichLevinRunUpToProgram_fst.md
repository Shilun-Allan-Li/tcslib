<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinRunUpToProgram_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of the Truncated Query Run

**Claim.** For every truncation stage, the output of the deterministic Goldreich–Levin query program is the state given by the stated recursion: it begins with the singleton empty set and empty trace, updates at eligible stages when the active family is within the cap, becomes absent when the family exceeds the cap, and otherwise retains the state.

**Proof.** Induct on the truncation index $k$. At zero, the program is pure and returns the initial state, so the claim follows directly. For the successor stage, let the previous program’s output be the previous state. The sequential-run identity (the output and additive cost law for `runWithCost_bind`) says that the new program first obtains this state, then runs the continuation selected by it. Replace the previous program’s output by the inductively identified state and split on whether $k<n$. If not, the continuation is pure and returns the state unchanged. If $k<n$ but the active family is absent, it again returns the state unchanged. If the family is present, split on whether its size is at most the active cap: when it is, the stage-step output theorem (`runWithCost_deterministicGoldreichLevinStageStepProgram_fst`) identifies the output with the prescribed query-state update; when it is not, the continuation returns the absent state while retaining the trace. These are precisely the cases in the recursive definition of the truncated state.

**Key facts.** `FABL.DeterministicQueryProgram.runWithCost_bind`, `FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageStepProgram_fst`.
