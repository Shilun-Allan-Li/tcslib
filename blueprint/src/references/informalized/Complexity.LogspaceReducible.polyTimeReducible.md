<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean :: Complexity.LogspaceReducible.polyTimeReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Implies Polynomial Time

**Claim.** For Boolean languages $B$ and $C$, if $B$ is logspace reducible to $C$, then $B$ is polynomial-time reducible to $C$.

**Proof.** Unpack the logspace reduction to obtain a function $f$ that is implicitly logspace computable and satisfies the reduction’s membership equivalence between $B$ and $C$. The fact that every implicitly logspace-computable function is polynomial-time computable (`Complexity.ImplicitlyLogspaceComputable.polyTimeComputable`) makes this same $f$ an admissible polynomial-time reduction. Its membership equivalence is unchanged, so it witnesses the claimed reduction.

**Key facts.** `Complexity.ImplicitlyLogspaceComputable.polyTimeComputable`.
