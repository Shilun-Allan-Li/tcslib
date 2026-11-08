<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFTerm.literalAt_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literal Selected from Its Support Coordinate

**Claim.** For any literal $\ell$ of $T$, the literal selected from the support of $T$ at coordinate $\ell$’s index is $\ell$.

**Proof.** The literal selected at coordinate $\ell$’s index belongs to $T$ (\texttt{literalAt\_mem}), and its index is that coordinate (\texttt{literalAt\_index}). The given literal $\ell$ also belongs to $T$. Since the literal coordinates in $T$ are pairwise distinct, two literals of $T$ with the same index must be equal (\texttt{eq\_of\_mem\_of\_index\_eq}). Applying this uniqueness to the selected literal and $\ell$ proves the claim.

**Key facts.** `FABL.DNFTerm.literalAt_mem`, `FABL.DNFTerm.literalAt_index`, `FABL.DNFTerm.eq_of_mem_of_index_eq`.
