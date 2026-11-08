<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of an Embedded Phase

**Claim.** Under the stated transition-agreement and state-guard hypotheses, the host run from the embedded, state-mapped source configuration reaches the corresponding embedded configuration at time $t$, and no host configuration through time $t$ has the anchor state.

**Proof.** For each time $j\le t$, the source run has only visited states satisfying the good-state predicate at all earlier times: every earlier time is strictly below $t$, so this is exactly the guard hypothesis. The state-map simulation theorem therefore identifies the host run from the state-mapped starting configuration at time $j$ with the state-mapped source run at time $j$ (Turing.MultiTapeTM.runFrom_mapState_of_agreeOn). The embedding-run identity rewrites the source and host runs of the embedded machines as embeddings of their respective source configurations (Turing.embedEmitTM_runFrom). At $j=t$, the assumed endpoint of the source run gives the claimed endpoint equality. For any $j\le t$, if the host configuration had state equal to the anchor, the run identity would imply that the mapped source state equals the anchor. A mapped state has the form $e(q)$, which cannot be the anchor by hypothesis. This proves safety at every time in the interval.

**Key facts.** `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Turing.embedEmitTM_runFrom`.
