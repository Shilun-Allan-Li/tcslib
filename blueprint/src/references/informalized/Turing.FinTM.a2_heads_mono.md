<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_heads_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of head bounds

**Claim.** If every work-tape head of a configuration lies in $[-A,A]$ and $A\le B$, then every such head lies in $[-B,B]$.

**Proof.** Fix a work tape. Its head position is at least $-A$ and at most $A$. Since $A\le B$, we have $-B\le -A$ and $A\le B$, so the same position lies between $-B$ and $B$. This holds for every work tape.
