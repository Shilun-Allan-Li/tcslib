<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.NPHard.polyTimeReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP-Hardness Under Polynomial-Time Reductions

**Claim.** If every language in $\mathsf{NP}$ reduces in polynomial time to $L$, and $L$ reduces in polynomial time to $L'$, then every language in $\mathsf{NP}$ reduces in polynomial time to $L'$.

**Proof.** Take any language $K\in\mathsf{NP}$. By the NP-hardness of $L$, there is a polynomial-time many-one reduction from $K$ to $L$. By assumption there is such a reduction from $L$ to $L'$. Polynomial-time many-one reductions compose: composing their reduction maps preserves the yes/no membership equivalence, and the composition is computable in polynomial time. Thus $K$ reduces to $L'$. Since this holds for every $K\in\mathsf{NP}$, $L'$ is NP-hard.

**Key facts.** `Complexity.PolyTimeReducible.trans`.
