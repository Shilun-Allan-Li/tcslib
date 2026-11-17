<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean :: Complexity.LogspaceReducible.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of Logspace Reducibility

**Claim.** For Boolean languages $B$, $C$, and $D$, if $B$ is logspace reducible to $C$ and $C$ is logspace reducible to $D$, then $B$ is logspace reducible to $D$.

**Proof.** Choose witnesses $f$ and $g$ for the two reductions, respectively. The composition $g\circ f$ is implicitly logspace computable by the composition theorem (`Complexity.ImplicitlyLogspaceComputable.comp`). For each input $x$, the first reduction identifies membership of $x$ in $B$ with membership of $f(x)$ in $C$, and the second identifies membership of $f(x)$ in $C$ with membership of $g(f(x))$ in $D$. Transitivity of logical equivalence gives the required membership equivalence for the composite, so it witnesses the reduction from $B$ to $D$.

**Key facts.** `Complexity.ImplicitlyLogspaceComputable.comp`.
