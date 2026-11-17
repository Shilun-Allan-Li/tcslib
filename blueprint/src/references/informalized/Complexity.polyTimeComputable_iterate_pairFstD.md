<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_iterate_pairFstD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Iterated First Projection

**Claim.** For each $n\in\mathbb{N}$, the $n$-fold iterate of the total first projection on bit strings is polynomial-time computable; its zeroth iterate is the identity.

**Proof.** Proceed by induction on $n$. At $n=0$, the iterate is the identity, which is polynomial-time computable (`polyTimeComputable_id`). For the successor step, the $(n+1)$-fold iterate is the first projection composed with the $n$-fold iterate. The first projection is polynomial-time computable, and the induction hypothesis gives the same for the $n$-fold iterate; closure under composition proves the successor case (`polyTimeComputable_pairFstD`, `PolyTimeComputable.comp`).

**Key facts.** `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`.
