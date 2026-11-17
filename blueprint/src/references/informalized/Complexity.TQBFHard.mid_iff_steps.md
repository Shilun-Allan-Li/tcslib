<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.mid_iff_steps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Midpoint relations and bounded step chains

**Claim.** For length-$w$ strings $A,B$, the midpoint relation of depth $r$ holds exactly when there is a chain of $2^r$ transitions from $A$ to $B$, with every intermediate string of length $w$ and every transition satisfying $E$.

**Proof.** Induct on $r$, with the assertion covering all endpoint strings of length $w$. At depth zero, the midpoint relation is simply $E(A,B)$, while a one-step chain consists of an intermediate string equal to $A$ followed by one $E$-transition; the two descriptions are equivalent. For the successor step, the step-chain addition law (Complexity.TQBFHard.steps_add) splits a chain of $2\cdot 2^r$ steps at a length-$w$ string $z$ into two chains of $2^r$ steps. By the induction hypothesis, these two chains are equivalent to the depth-$r$ midpoint relations from $A$ to $z$ and from $z$ to $B$. Requiring such a midpoint $z$ is exactly the recursive definition of the depth-$(r+1)$ relation.

**Key facts.** `Complexity.TQBFHard.steps_add`.
