<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.canonicalTerm_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership of the Canonical Term

**Claim.** If at least one term is compatible with $\rho$, then the canonical term selected for $\rho$ belongs to the list of terms of $\phi$.

**Proof.** The canonical index is an index into the finite list of terms. The canonical term is the list entry at that index, and every list entry at a valid index belongs to the list. Hence the canonical term is a member of $\phi$'s terms.
