<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.val_all -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Quantifier Branching

**Claim.** When the $k$th bit of the prefix is false, the valuation at $(k,S)$ holds exactly when it holds for both next-level encodings $(k+1,2S)$ and $(k+1,2S+1)$.

**Proof.** Since $k$ is a valid prefix index, the quantifier list remaining after position $k$ begins with the quantifier represented by the bit $q_k$. The decomposition of the mapped suffix at a valid index (`Complexity.LogProg.TQBFARM.drop_map_eq`) makes this first quantifier explicit; as $q_k$ is false, it is universal. Thus the defining clause for quantified truth says that the valuation holds precisely when the remaining formula holds after updating variable $k$ to each Boolean value. The assignment update identity (`Complexity.LogProg.TQBFARM.asg_push`) identifies these two updated assignments with the encodings at $(k+1,2S)$ and $(k+1,2S+1)$, respectively. Consequently, the universal condition is exactly the conjunction of the two stated valuations.

**Key facts.** `Complexity.LogProg.TQBFARM.drop_map_eq`, `Complexity.LogProg.TQBFARM.asg_push`.
