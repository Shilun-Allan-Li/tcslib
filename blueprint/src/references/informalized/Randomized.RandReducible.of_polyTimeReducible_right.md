<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPOperator.lean :: Randomized.RandReducible.of_polyTimeReducible_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composing Randomized and Polynomial Reductions

**Claim.** If $A$ is randomized-reducible to $B$ and $B$ is polynomial-time reducible to $C$, then $A$ is randomized-reducible to $C$.

**Proof.** Let $f$ witness the randomized reduction from $A$ to $B$, with its probability guarantee, and let $g$ be a polynomial-time many-one reduction from $B$ to $C$. Use the composed map $g\circ f$. It is polynomial-time by closure of polynomial-time computability under composition (`PolyTimeComputable.comp`). For each input and each random string, membership of the original randomized output in $B$ is equivalent, by the many-one reduction, to membership of its image under $g$ in $C$. Therefore the success event has the same probability after composition (`randProb_congr`), and the original probability guarantee carries over unchanged.

**Key facts.** `Complexity.PolyTimeComputable.comp`, `Randomized.randProb_congr`.
