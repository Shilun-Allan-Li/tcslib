<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourProgram_queries_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership-query cost bound

**Claim.** For every supported outcome of the Kushilevitz–Mansour program, its membership-query count is at most the Goldreich–Levin query budget plus $640A^4/\varepsilon^2$, where $A$ is the active cap at threshold $\tau=\varepsilon/(4M)$.

**Proof.** First decompose the supported full-run outcome into a supported Goldreich–Levin outcome and a supported second-stage outcome, with their costs summing componentwise (`FABL.kushilevitzMansourProgram_cost_decomposition`). The Goldreich–Levin query-count bound gives the first-stage count at most its query budget (`FABL.goldreichLevinQueryProgram_queries_le`); cast this natural-number inequality to the rationals. The second-stage query-count bound gives at most $640A^4/\varepsilon^2$ (`FABL.kushilevitzMansourSecondStage_queries_cast_le`). By the cost decomposition, the total query count is the sum of these two stage counts. Adding their respective bounds proves the claimed inequality.

**Key facts.** `FABL.kushilevitzMansourProgram_cost_decomposition`, `FABL.goldreichLevinQueryProgram_queries_le`, `FABL.kushilevitzMansourSecondStage_queries_cast_le`.
