<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.PSPACE_eq_P_of_pspaceComplete_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A polynomial-space complete language in polynomial time

**Claim.** If a polynomial-space complete language is decidable in polynomial time, then polynomial space equals polynomial time.

**Proof.** For any language in $	extsf{PSPACE}$, completeness gives a polynomial-time many-one reduction to $L'$. Since $L'$ is in $	extsf{P}$, closure of $	extsf{P}$ under polynomial-time many-one reductions (`Complexity.mem_P_of_polyTimeReducible`) puts the original language in $	extsf{P}$. Thus $	extsf{PSPACE}\subseteq\textsf{P}$. The reverse inclusion is `Complexity.P_subset_PSPACE`, so the classes are equal.

**Key facts.** `Complexity.mem_P_of_polyTimeReducible`, `Complexity.P_subset_PSPACE`.
