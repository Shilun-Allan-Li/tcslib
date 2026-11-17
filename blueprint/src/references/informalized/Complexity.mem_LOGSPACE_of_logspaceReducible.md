<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean :: Complexity.mem_LOGSPACE_of_logspaceReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure of Log Space Under Reductions

**Claim.** If $B$ is log-space reducible to $C$ and $C$ is decidable in logarithmic space, then $B$ is decidable in logarithmic space.

**Proof.** Unpack the reduction: there is a log-space computable function $f$ such that, for every input $x$, $x\in B$ exactly when $f(x)\in C$. Thus $B$ is the preimage of $C$ under $f$. Log-space closure under such preimages (`Complexity.mem_LOGSPACE_preimage`) now gives that $B$ belongs to LOGSPACE.

**Key facts.** `Complexity.mem_LOGSPACE_preimage`.
