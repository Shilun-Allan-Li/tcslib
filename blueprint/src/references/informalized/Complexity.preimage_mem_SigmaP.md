<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.preimage_mem_SigmaP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential hierarchy preimage closure

**Claim.** For each $i\in\mathbb N$, if $L$ belongs to the $i$th existential level of the polynomial hierarchy and $f$ is polynomial-time computable, then $\{x:f(x)\in L\}$ belongs to that same level.

**Proof.** The $i$th existential level is the alternating class with first quantifier existential. Apply preimage closure for alternating classes (`preimage_mem_altClass`) to $L$ and the polynomial-time computable function $f$. The resulting preimage belongs to the same alternating class, which is exactly the $i$th existential level.

**Key facts.** `Turing.Complexity.PolyHierarchy.preimage_mem_altClass`.
