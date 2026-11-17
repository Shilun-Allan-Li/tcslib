<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.compl_mem_PiP_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Characterization of Universal Levels

**Claim.** For every $i\ge 0$ and binary language $L$, $L^c\in\Pi_i^P$ if and only if $L\in\Sigma_i^P$.

**Proof.** By definition, membership of a language $A$ in $\Pi_i^P$ means that its complement belongs to $\Sigma_i^P$. Taking $A=L^c$, the left side is therefore equivalent to $(L^c)^c\in\Sigma_i^P$. Since taking complements twice returns $L$, this is exactly $L\in\Sigma_i^P$.
