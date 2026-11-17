<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean :: Complexity.TQBFHard.steps_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of step counts

**Claim.** If $E$ is reflexive, $k\le k'$, and $B$ has length $w$, then any $k$-step chain from $A$ to $B$ extends to a $k'$-step chain with the same endpoints.

**Proof.** Write $k'=k+d$ for some natural number $d$. Induct on $d$. If $d=0$, the given chain already has the required length. For the successor case, use the induction hypothesis to obtain a $(k+d)$-step chain from $A$ to $B$. The definition of a successor-length chain allows one more step by choosing the intermediate string to be $B$ itself: it has length $w$, and the final edge $E(B,B)$ holds by reflexivity.
