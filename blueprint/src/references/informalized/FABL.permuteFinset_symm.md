<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.permuteFinset_symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse permutation of a finite set

**Claim.** For a permutation $\pi$ of $\mathrm{Fin}\,n$ and a finite set $S$, applying $\pi^{-1}$ to $S$ and then applying $\pi$ returns $S$.

**Proof.** Mapping a finite set by an embedding and then by another embedding is the same as mapping it by their composition. Here the two embeddings are induced by $\pi^{-1}$ and $\pi$, whose composition is the identity. Mapping $S$ by the identity leaves it unchanged.
