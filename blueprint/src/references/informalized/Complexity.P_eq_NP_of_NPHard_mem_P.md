<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.P_eq_NP_of_NPHard_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An NP-hard language in polynomial time collapses P and NP

**Claim.** If an NP-hard language is decidable in polynomial time, then $	extsf{P}=	extsf{NP}$.

**Proof.** Polynomial time is contained in $	extsf{NP}$ (`Complexity.P_subset_NP`), giving one inclusion. For the reverse, take any language in $	extsf{NP}$. Its reduction to the NP-hard language $L$ is a polynomial-time many-one reduction; because $L$ is in $	extsf{P}$, closure of $	extsf{P}$ under such reductions (`Complexity.mem_P_of_polyTimeReducible`) puts the language in $	extsf{P}$. Hence $	extsf{NP}\subseteq\textsf{P}$, and the two inclusions give equality.

**Key facts.** `Complexity.P_subset_NP`, `Complexity.mem_P_of_polyTimeReducible`.
