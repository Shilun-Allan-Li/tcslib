<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.PiP_subset_SigmaP_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pi-to-Sigma Level Inclusion

**Claim.** For every $i\in\mathbb{N}$, every language in $\Pi_i^P$ belongs to $\Sigma_{i+1}^P$.

**Proof.** Let $L\in\Pi_i^P$. The characterization of the next Sigma level says it suffices to find a language $L'$ in $\Pi_i^P$ such that membership in $L$ is equivalent to the existence of a polynomially bounded witness $u$ with the pair encoding of the input and witness in $L'$. Choose $L'$ to be the preimage of $L$ under the total first projection, and use zero as both polynomial bounds. The preimage remains in $\Pi_i^P$ because the projection is polynomial-time computable (\texttt{preimage\_mem\_PiP}, \texttt{polyTimeComputable\_pairFstD}). The zero-length witness is necessarily the empty string. For every input $x$, the first projection of its pair encoding with the empty string is exactly $x$ (\texttt{pairFstD\_pairEncode}); thus the existential condition is equivalent to $x\in L$, as required by the characterization (\texttt{mem\_SigmaP\_succ\_iff}).

**Key facts.** `Complexity.mem_SigmaP_succ_iff`, `Complexity.preimage_mem_PiP`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.pairFstD_pairEncode`.
