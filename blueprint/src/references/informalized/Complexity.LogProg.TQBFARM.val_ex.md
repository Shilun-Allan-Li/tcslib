<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.val_ex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential Quantifier Branching

**Claim.** When the $k$th bit of the prefix is true, the valuation at $(k,S)$ holds exactly when at least one of the next-level valuations at $(k+1,2S)$ and $(k+1,2S+1)$ holds.

**Proof.** Because $k$ is a valid prefix index, the remaining mapped prefix begins with the quantifier represented by $q_k$ (`Complexity.LogProg.TQBFARM.drop_map_eq`). The bit is true, so this quantifier is existential, and the defining clause for quantified truth says that some Boolean value for variable $k$ makes the remaining formula true. By the assignment update identity (`Complexity.LogProg.TQBFARM.asg_push`), choosing false gives the encoding $(k+1,2S)$, while choosing true gives $(k+1,2S+1)$. Existence of such a Boolean is therefore equivalent to the disjunction of those two next-level valuations.

**Key facts.** `Complexity.LogProg.TQBFARM.drop_map_eq`, `Complexity.LogProg.TQBFARM.asg_push`.
