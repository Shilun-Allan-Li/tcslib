<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.canonicalTerm_eq_of_extends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Term Under Extension

**Claim.** If $\eta$ extends $\rho$, both restrictions admit compatible terms, and the canonical term selected for $\rho$ is compatible with $\eta$, then the canonical terms selected for $\rho$ and $\eta$ are equal.

**Proof.** The canonical term is the term in the list at the canonical index. The canonical-index extension result (`DNFFormula.canonicalTermIndex_eq_of_extends`) gives equality of the two indices under the stated hypotheses. Reading the same list at equal indices yields equal terms.

**Key facts.** `FABL.DNFFormula.canonicalTermIndex_eq_of_extends`.
