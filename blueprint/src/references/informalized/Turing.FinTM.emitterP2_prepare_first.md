<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_prepare_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Completed Preparation Frame

**Claim.** The preparation machine reaches the specified completed frame at some positive time bounded by $5(|s|+|w|+3)$, and before that time it does not visit phase $8$.

**Proof.** First use the preparation-run result to obtain a time $T$ within the stated bound at which the machine has the specified frame in phase $8$ (Turing.FinTM.emitterP2_prepare_run). Phase $8$ is a stopping phase: its transition leaves the configuration fixed. Therefore the first-entry lemma applies to the run ending at time $T$ and gives a time $t\le T$ at which the endpoint frame is reached, with no earlier configuration in phase $8$ (Turing.FinTM.emitter_first_entry). The resulting time is positive: if it were zero, the endpoint configuration would equal the initial configuration, but their states have different phase coordinates, $8$ and $0$. Consequently $0<t\le T$, so the same numerical bound holds, and the first-entry property is exactly the required avoidance of phase $8$ before $t$.

**Key facts.** `Turing.FinTM.emitterP2_prepare_run`, `Turing.FinTM.emitter_first_entry`.
