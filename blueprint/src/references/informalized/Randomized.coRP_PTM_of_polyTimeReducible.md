<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.coRP_PTM_of_polyTimeReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure of coRP Under Reductions

**Claim.** If $L'$ is polynomial-time many-one reducible to $L$ and $L$ belongs to coRP, then $L'$ belongs to coRP.

**Proof.** Translate the assumption that $L$ belongs to coRP into the equivalent statement that $L$ is recognized by the corresponding coRP verifier model (mem_coRP_PTM_iff). The closure theorem for that model says that polynomial-time many-one reductions preserve membership: from $L'\le_p L$ and this recognition of $L$, it gives the same coRP-model membership for $L'$ (InCoRP.of_polyTimeReducible). Translating back with the membership equivalence yields $L'\in\mathrm{coRP}$.

**Key facts.** `Randomized.mem_coRP_PTM_iff`, `Randomized.InCoRP.of_polyTimeReducible`.
