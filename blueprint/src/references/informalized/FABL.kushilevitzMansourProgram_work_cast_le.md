<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourProgram_work_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local-work bound for the learner

**Claim.** For every output and cost pair in the support of the Kushilevitz–Mansour program, the charged local work is at most the Goldreich–Levin work budget plus $1280A^4(n+1)/\varepsilon^2$, with $A$ and the threshold as specified.

**Proof.** Decompose a supported run into a first outcome from the Goldreich–Levin query program and a second outcome from the Kushilevitz–Mansour second stage. The decomposition preserves the output and expresses the total cost as the sum of the two costs (\texttt{kushilevitzMansourProgram\_cost\_decomposition}). The first outcome's work is bounded by the Goldreich–Levin work budget (\texttt{goldreichLevinQueryProgram\_work\_le}); casting that natural-number inequality to rationals gives the first term in the desired bound. The second-stage work is at most $1280A^4(n+1)/\varepsilon^2$ (\texttt{kushilevitzMansourSecondStage\_work\_cast\_le}). Since the total work is the sum of these two work counts, adding their respective bounds proves the result.

**Key facts.** `FABL.kushilevitzMansourProgram_cost_decomposition`, `FABL.goldreichLevinQueryProgram_work_le`, `FABL.kushilevitzMansourSecondStage_work_cast_le`.
