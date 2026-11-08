<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/CoNP.lean :: Complexity.P_subset_NP_inter_coNP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time and Its Complements

**Claim.** Every language in polynomial time belongs to both $\mathsf{NP}$ and $\mathsf{coNP}$, so $\mathsf{P} \subseteq \mathsf{NP} \cap \mathsf{coNP}$.

**Proof.** Take a language $L$ in $\mathsf{P}$. The polynomial-time-to-NP inclusion gives $L \in \mathsf{NP}$ (\(\texttt{Complexity.P\_subset\_NP}\)). Also, polynomial time is closed under complement, so $L^c \in \mathsf{P}$ (\(\texttt{Complexity.compl\_mem\_P}\)); applying the same inclusion gives $L^c \in \mathsf{NP}$, which is precisely $L \in \mathsf{coNP}$. Thus $L$ belongs to the intersection.

**Key facts.** `Complexity.P_subset_NP`, `Complexity.compl_mem_P`.
