<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPOperator.lean :: Randomized.RandReducible.refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of randomized reducibility

**Claim.** Every language of bit strings is randomized reducible to itself.

**Proof.** Use the identity map on bit strings. It is polynomial-time computable, and for every input string, membership in the language is equivalent to membership of its image under the identity map. Thus it gives a polynomial-time reduction from the language to itself; every such reduction is also a randomized reduction by the theorem that polynomial-time reducibility implies randomized reducibility (`RandReducible.of_polyTimeReducible`).

**Key facts.** `Randomized.RandReducible.of_polyTimeReducible`, `Complexity.polyTimeComputable_id`.
