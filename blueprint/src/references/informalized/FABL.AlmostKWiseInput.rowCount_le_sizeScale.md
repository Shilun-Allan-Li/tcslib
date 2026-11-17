<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.AlmostKWiseInput.rowCount_le_sizeScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row count bounded by the size scale

**Claim.** For row count $r=(k-1)d+1$ and size scale $s=k(d+1)$, one has $r\le s$.

**Proof.** Because $k\ge1$, we have $k-1\le k$ and $1\le k$. Multiplying the first inequality by the nonnegative field degree $d$ and adding the second gives $(k-1)d+1\le kd+k$. Rearranging the right-hand side as $k(d+1)$ proves the claim.
