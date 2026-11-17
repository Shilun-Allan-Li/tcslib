<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.mem_PiP_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal-Quantifier Characterization of $\Pi_i^P$

**Claim.** For every $i$ and language $L$, membership in $\Pi_i^P$ is equivalent to having a polynomially bounded alternating-quantifier characterization beginning with a universal quantifier and ending in a polynomial-time language.

**Proof.** The complement characterization for alternating classes says that $L^c\in\mathrm{altClass}(b,i)$ exactly when $L\in\mathrm{altClass}(\neg b,i)$ (`Complexity.compl_mem_altClass_iff`). By the definition of $\Pi_i^P$, its membership condition is $L^c\in\Sigma_i^P=\mathrm{altClass}(\mathrm{true},i)$. Applying the complement characterization with the existential first quantifier changes that first quantifier to universal, giving precisely the stated witnesses, polynomial bound, and equivalence.

**Key facts.** `Complexity.compl_mem_altClass_iff`.
