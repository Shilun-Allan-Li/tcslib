<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.preimage_mem_PiP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal hierarchy preimage closure

**Claim.** For each $i\in\mathbb N$, if $L$ belongs to the $i$th universal level of the polynomial hierarchy and $f$ is polynomial-time computable, then $\{x:f(x)\in L\}$ belongs to that same level.

**Proof.** Identify the $i$th universal level with the alternating class whose first quantifier is universal (`PiP_eq_altClass`). Under this identification, the hypothesis says $L$ belongs to that alternating class. Preimages under polynomial-time computable functions preserve every alternating class (`preimage_mem_altClass`), so the preimage of $L$ belongs to the corresponding class as well. Converting back with the same identification gives the result.

**Key facts.** `Complexity.PiP_eq_altClass`, `Complexity.PolyHierarchy.preimage_mem_altClass`.
