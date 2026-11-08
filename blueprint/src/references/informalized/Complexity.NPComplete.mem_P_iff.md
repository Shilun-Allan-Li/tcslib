<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.NPComplete.mem_P_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time and NP-Completeness

**Claim.** For an NP-complete language $L$, membership $L\in\mathsf{P}$ is equivalent to $\mathsf{P}=\mathsf{NP}$.

**Proof.** Suppose first that $L\in\mathsf{P}$. Since $L$ is NP-hard, the theorem that an NP-hard language in polynomial time forces $\mathsf{P}=\mathsf{NP}$ applies. Conversely, suppose $\mathsf{P}=\mathsf{NP}$. NP-completeness includes $L\in\mathsf{NP}$, so substituting the assumed equality gives $L\in\mathsf{P}$.

**Key facts.** `Complexity.P_eq_NP_of_NPHard_mem_P`.
