<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_segments -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work head bounds across segments

**Claim.** If the stated bounded segments link successive configurations and the final segment either halts or reaches the next configuration, then every head in the run from $c_0$ remains in $[-B,B]$.

**Proof.** Induct on the number $N$ of segments. The zero-segment case is impossible under $N>0$. For the successor case, take the bounded segment starting at $c_0$ and let $u$ be its endpoint. If the requested time $t$ is at most $u$, its head bounds follow directly from the segment hypothesis. Otherwise write $t=u+(t-u)$ and split the run at time $u$ using the run composition law `runFrom_add`. If the endpoint configuration is halted, the run stays there by `runFrom_of_halt`, so its heads satisfy the bounds already established at time $u$. If instead the endpoint equals $c_1$, reindex the remaining segment sequence by sending index $i$ to $c_{i+1}$. The segment hypotheses persist under this reindexing, with one fewer segment; the induction hypothesis bounds the run from $c_1$ at time $t-u$. Composing the first segment with this tail proves the bound at the original time.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
