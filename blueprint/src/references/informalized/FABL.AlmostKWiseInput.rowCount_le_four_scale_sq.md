<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.AlmostKWiseInput.rowCount_le_four_scale_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row count bounded by the squared scale

**Claim.** With field degree $d$, scale $s$, and row count $r=(k-1)d+1$, the row count satisfies $r\le 4(s+1)^2$.

**Proof.** First bound the row count by the size scale $k(d+1)$, using the row-count-to-size-scale estimate (`FABL.AlmostKWiseInput.rowCount_le_sizeScale`). Since $k\le n$, this size scale is at most $n(d+1)$. The dimension-to-scale estimate gives $n\le s$ (`FABL.AlmostKWiseInput.n_le_scale`), while the field-degree estimate gives $d+1\le 4(n+1)$ (`FABL.ExecutableVandermondeInput.fieldDegree_succ_le`). Together these yield $n(d+1)\le s\cdot 4(s+1)$. Finally, $s\le s+1$, so this is at most $4(s+1)^2$, as required.

**Key facts.** `FABL.AlmostKWiseInput.rowCount_le_sizeScale`, `FABL.AlmostKWiseInput.n_le_scale`, `FABL.ExecutableVandermondeInput.fieldDegree_succ_le`.
