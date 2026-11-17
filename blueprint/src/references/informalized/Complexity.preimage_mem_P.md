<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.preimage_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time preimage closure

**Claim.** If $V$ belongs to $\mathsf P$ and $g$ is polynomial-time computable, then the preimage $\{x:g(x)\in V\}$ belongs to $\mathsf P$.

**Proof.** Represent membership of $V$ in $\mathsf P$ by its polynomial-time Boolean indicator function, using the characterization of $\mathsf P$ by polynomial-time computability (`mem_P_iff_polyTimeComputable`). Compose that indicator with $g$; polynomial-time computability is preserved under composition (`PolyTimeComputable.comp`). The resulting function maps $x$ to the one-bit indicator of whether $g(x)$ belongs to $V$, so by the same characterization its accepted language is in $\mathsf P$. This language is precisely the preimage of $V$ under $g$.

**Key facts.** `Complexity.mem_P_iff_polyTimeComputable`, `Complexity.PolyTimeComputable.comp`.
