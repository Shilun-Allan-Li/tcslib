<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.canonicalTerm_compatible' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility of the Canonical Term

**Claim.** If at least one term of $\phi$ is compatible with $\rho$, then the canonical term selected by least index is compatible with $\rho$.

**Proof.** By definition, the canonical term is the term of $\phi$ at its canonical index. The canonical-index compatibility result (`DNFFormula.canonicalTerm_compatible`) says that this indexed term is compatible with $\rho$. Substituting the definition of the canonical term gives the claim.

**Key facts.** `FABL.DNFFormula.canonicalTerm_compatible`.
