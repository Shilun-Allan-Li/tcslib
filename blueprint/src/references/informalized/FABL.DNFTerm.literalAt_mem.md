<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFTerm.literalAt_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected Literal Belongs to the Term

**Claim.** If $i$ belongs to the support of $T$, then the literal selected at coordinate $i$ is one of the literals of $T$.

**Proof.** Membership of $i$ in the support means that some literal in the list of $T$ has index $i$. The definition of the selected literal chooses such a literal, so it belongs to the list of literals of $T$.
