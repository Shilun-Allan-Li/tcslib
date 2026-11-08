<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.canonicalTerm_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width Bound for the Canonical Term

**Claim.** If the width of $\phi$ is at most $w$ and at least one term is compatible with $\rho$, then the canonical term selected for $\rho$ has width at most $w$.

**Proof.** The canonical term belongs to the list of terms of $\phi$ (`DNFFormula.canonicalTerm_mem`). Every term in that list has width at most the formula's width (`DNFFormula.width_le_of_mem`). Combining this bound with $\phi$'s width being at most $w$ proves the result.

**Key facts.** `FABL.DNFFormula.canonicalTerm_mem`, `FABL.DNFFormula.width_le_of_mem`.
