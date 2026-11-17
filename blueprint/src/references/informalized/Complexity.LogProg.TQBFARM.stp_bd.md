<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.stp_bd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Initial State

**Claim.** If $k$, $S$, and $p$ are each at most $B$, then the state with those values in the depth, stack, and input-pointer registers, and zeros in all four scratch registers, has every register at most $B$.

**Proof.** By definition, the bound on a state is the conjunction of the seven individual register bounds. The first three are the hypotheses $k\le B$, $S\le B$, and $p\le B$. Each remaining register is $0$, which is at most the natural number $B$.
