<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.reach_iff_walkLe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Reachability by Walks

**Claim.** For endpoints $c,t<n$, a finite path using steps of $E$ whose vertices remain below $n$ exists exactly when there is a walk from $c$ to $t$ of length at most $n$, with all intermediate vertices below $n$.

**Proof.** For the forward implication, the existence theorem for bounded walks supplies some length $j$ and a walk of length $j$ from $c$ to $t$ (`Complexity.exists_walkLe`). Since the target is below $n$ (and the source is below $n$ by hypothesis), the shortening result replaces this bound $j$ by $n$, preserving the walk (`Complexity.walkLe_short`). Conversely, a walk of bound $n$ yields a reflexive-transitive path in the relation that requires both endpoints of each step to be below $n$ (`Complexity.walkLe_reach`). This includes the zero-length case, where the endpoints coincide.

**Key facts.** `Complexity.exists_walkLe`, `Complexity.walkLe_short`, `Complexity.walkLe_reach`.
