<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.stage_consistent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Consistency of stage queries

**Claim.** For each query string $z$ made at stage $i$, membership in the positive oracle at stage $i$ is equivalent to membership in the oracle formed by the union of positive strings over all stages.

**Proof.** Fix a query $z$ made at stage $i$. If $z$ is positive at stage $i$, it belongs to the union oracle by definition. Conversely, suppose $z$ belongs to that union. Then it first enters the positive sets at some stage $s+1$: this is `Complexity.exists_entry`. Compare $s$ with $i$.

1. If $s<i$, positivity persists through later stages, by monotonicity of the positive sets (`Complexity.stage_pos_mono`), so $z$ is positive at stage $i$.
2. If $s=i$, the stage transition identifies a newly added string as the selected stage witness (`Complexity.stage_new`). That witness is absent from the stage query list by `Complexity.stageWit_spec`, contradicting that $z$ is a query at stage $i$.
3. If $i<s$, every query made during stage $i$ has length at most its running time, by `Turing.OracleTM.length_le_of_mem_queriesWithin`. But $z$ enters at stage $s+1$ with length equal to the fresh length for stage $s$, by `Complexity.entry_length`; the later-stage bound says this length exceeds the stage-$i$ running time (`Complexity.stage_later`). This contradicts the query-length bound.

Only the first case can occur, proving that $z$ was already positive at stage $i$ and hence establishing the equivalence.

**Key facts.** `Complexity.exists_entry`, `Complexity.stage_pos_mono`, `Complexity.stage_new`, `Complexity.stageWit_spec`, `Turing.OracleTM.length_le_of_mem_queriesWithin`, `Complexity.entry_length`, `Complexity.stage_later`.
