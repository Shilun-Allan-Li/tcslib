<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Engine.lean :: Complexity.Codec.incChain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Chain of Register Increments

**Claim.** If each of the first $k$ labels increments register $r$ and advances to the next label, then the program reaches label $k$ from label zero with $r$ increased by $k$ and all other registers unchanged. The safety condition holds throughout, and every register remains at most $B$.

**Proof.** Apply the general register-chain theorem (`arm_chain`) in its increment case. Its label condition says exactly that each instruction along the chain increments $r$ and advances one index. The bound $v(r)+k\le B$ is the increment-case resource hypothesis, while the bounds on all initial registers supply the remaining hypotheses. The theorem therefore gives a run from label zero to label $k$, with $r$ increased by $k$ (the update leaves all other registers unchanged), and ensures that the prescribed guard and register bounds hold throughout.

**Key facts.** `Complexity.LogProg.arm_chain`.
