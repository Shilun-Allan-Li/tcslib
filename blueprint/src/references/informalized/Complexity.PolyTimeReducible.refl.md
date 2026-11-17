<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.PolyTimeReducible.refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of polynomial-time reducibility

**Claim.** Every language $L$ over the binary alphabet is polynomial-time Karp reducible to itself.

**Proof.** Use the identity function as the reduction. It is polynomial-time computable (`Complexity.polyTimeComputable_id`), and for every string $x$, membership of $x$ in $L$ is equivalent to membership of the same string $x$ in $L$. This is exactly the condition for the reduction from $L$ to itself.

**Key facts.** `Complexity.polyTimeComputable_id`.
